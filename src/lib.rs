#![crate_name = "polymap"]
#![allow(unstable)]
#![feature(unsafe_destructor)]

use std::borrow::BorrowFrom;
use std::intrinsics::{get_tydesc, TyDesc, TypeId};
use std::mem::{align_of, size_of};
use std::ptr;
use std::slice::Iter;

fn align(offset: usize, alignment: usize) -> usize {
    match offset % alignment {
        0 => offset,
        n => offset + (alignment - n),
    }
}

/// A key-value map that can contain varying types of values.
///
/// A single `PolyMap` instance can map a given key to varying types of values.
/// Successive operations on this key must use the correct type or the operation
/// will panic.
///
/// # Example
///
/// ```
/// use polymap::PolyMap;
///
/// let mut map = PolyMap::new();
///
/// // Maps `&str` to `&str`.
/// map.insert("foo", "Hello, world!");
///
/// // Maps `&str` to `i32`.
/// map.insert("bar", 123);
///
/// // Gets a reference to the stored member.
/// let foo: &&str = map.get("foo").unwrap();
/// println!("Got our string back: {}", foo);
///
/// let bar: &i32 = map.get("bar").unwrap();
/// println!("And here's our i32: {}", bar);
/// ```
///
/// # Notes
///
/// Values are stored in an internal buffer that is reallocated when exhausted.
/// Methods `reserve_data`, `reserve_data_exact`, and constructor `with_capacity`
/// can be used to reserve a larger buffer ahead of time to prevent expensive
/// reallocation and move operations.
///
#[derive(Default)]
pub struct PolyMap<K> {
    /// Value data store
    data: Vec<u8>,
    /// Inserted fields
    fields: Vec<Field<K>>,
}

/// Private `PolyMap` field descriptor.
///
/// Contains the field key and size and offset, as well as `TypeId`,
/// which is used to identify a type for successive operations, and `TyDesc`,
/// which is used to call a destructor ("drop glue") when `PolyMap::clear`
/// is called or a `PolyMap` instance goes out of scope.
struct Field<K> {
    key: K,
    offset: usize,
    size: usize,
    id: TypeId,
    tydesc: *const TyDesc,
}

impl<K: Eq> PolyMap<K> {
    /// Constructs a new `PolyMap`.
    pub fn new() -> PolyMap<K> {
        PolyMap{
            data: Vec::new(),
            fields: Vec::new(),
        }
    }

    /// Constructs a new `PolyMap` with space reserved for `n` fields
    /// and `size` bytes of data.
    pub fn with_capacity(n: usize, size: usize) -> PolyMap<K> {
        PolyMap{
            data: Vec::with_capacity(size),
            fields: Vec::with_capacity(n),
        }
    }

    /// Removes all key-value pairs from the map, calling any destructors on
    /// stored values.
    pub fn clear(&mut self) {
        while let Some(f) = self.fields.pop() {
            let tydesc: &TyDesc = unsafe { &*f.tydesc };
            (tydesc.drop_glue)(self.get_data::<i8>(f.offset));
        }
    }

    /// Returns whether the map contains a value corresponding to the given key.
    /// Does not make any assertions about the type of the value.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
            where Q: Eq + BorrowFrom<K> {
        self.get_field(k).is_some()
    }

    /// Returns whether the map contains a value corresponding to the given key
    /// whose type is the same as the given type.
    ///
    /// # Example
    ///
    /// ```
    /// use polymap::PolyMap;
    ///
    /// let mut map = PolyMap::new();
    ///
    /// map.insert("foo", 1);
    /// assert_eq!(false, map.contains_key_of::<_, &str>("foo"));
    /// assert_eq!(true, map.contains_key_of::<_, i32>("foo"));
    /// ```
    pub fn contains_key_of<Q: ?Sized, T: 'static>(&self, k: &Q) -> bool
            where Q: Eq + BorrowFrom<K> {
        let id = TypeId::of::<T>();
        self.get_field(k).map(|f| f.id == id) == Some(true)
    }

    /// Returns the capacity, in bytes, of the internal data buffer.
    pub fn data_capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Returns the size, in bytes, of the internal data buffer.
    pub fn data_size(&self) -> usize {
        self.data.len()
    }

    /// Returns a reference to the value corresponding to the given key.
    ///
    /// If the key is not contained within the map, `None` will be returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn get<Q: ?Sized, T: 'static>(&self, k: &Q) -> Option<&T>
            where Q: Eq + BorrowFrom<K> {
        self.get_field_with_id(k, TypeId::of::<T>())
            .map(|f| unsafe { &*self.get_data(f.offset) })
    }

    /// Returns a mutable reference to the value corresponding to the given key.
    ///
    /// If the key is not contained within the map, `None` will be returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn get_mut<Q: ?Sized, T: 'static>(&mut self, k: &Q) -> Option<&mut T>
            where Q: Eq + BorrowFrom<K> {
        self.get_field_with_id(k, TypeId::of::<T>())
            .map(|f| f.offset)
            .map(|offset| unsafe { &mut *self.get_data_mut(offset) })
    }

    /// Inserts a key-value pair into the map. If the key is already present,
    /// that value is returned. Otherwise, `None` is returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but has a value of a different type than the one given.
    pub fn insert<T: 'static>(&mut self, k: K, t: T) -> Option<T> {
        let offset = self.get_field(&k).map(|f| {
            if f.id != TypeId::of::<T>() {
                panic!("insert with value of different type");
            }
            f.offset
        });

        unsafe {
            if let Some(offset) = offset {
                Some(ptr::replace(self.get_data_mut(offset), t))
            } else {
                let offset = self.allocate::<T>(k);
                ptr::write(self.get_data_mut(offset), t);
                None
            }
        }
    }

    /// Returns an iterator visiting all keys in arbitrary order.
    /// Iterator element type is `&K`.
    pub fn keys(&self) -> Keys<K> {
        Keys{iter: self.fields.iter()}
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.fields.len()
    }

    /// Reserves capacity for at least `additional` additional bytes of storage
    /// space within the internal data buffer.
    pub fn reserve_data(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    /// Reserves space for at least `n` bytes in the internal data buffer.
    /// Does nothing if the capacity is already sufficient.
    pub fn reserve_data_exact(&mut self, n: usize) {
        self.data.reserve_exact(n);
    }

    /// Reserves capacity for at least `additional` additional fields.
    pub fn reserve_fields(&mut self, additional: usize) {
        self.fields.reserve(additional);
    }

    /// Reserves space for at least `n` fields.
    /// Does nothing if the capacity is already sufficient.
    pub fn reserve_fields_exact(&mut self, n: usize) {
        self.fields.reserve_exact(n);
    }

    /// Removes a key from the map, returning the value if one existed.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn remove<Q: ?Sized, T: 'static>(&mut self, k: &Q) -> Option<T>
            where Q: Eq + BorrowFrom<K> {
        let id = TypeId::of::<T>();

        let pos = self.fields.iter().position(|f| {
            if k.eq(BorrowFrom::borrow_from(&f.key)) {
                if f.id != id {
                    panic!("remove value of a different type");
                }
                true
            } else {
                false
            }
        });

        pos.map(|pos| {
            let f = self.fields.remove(pos);
            unsafe {
                let p = self.get_data(f.offset);
                ptr::read(p)
            }
        })
    }

    /// Shrinks the internal data buffer as close as possible to the size of
    /// the currently contained elements.
    pub fn shrink_data_to_fit(&mut self) {
        // TODO: Make an effort to condense elements within allocated space
        self.data.shrink_to_fit();
    }

    /// Allocates space for an object of given size and alignment.
    /// Grows buffer if necessary. Returns offset of new object.
    fn allocate<T: 'static>(&mut self, k: K) -> usize {
        let size = size_of::<T>();
        let alignment = align_of::<T>();
        let id = TypeId::of::<T>();

        let (offset, index) = if self.fields.is_empty() {
            (0, 0)
        } else if size <= self.fields[0].offset {
            (0, 0)
        } else {
            let ia = self.fields.iter();
            let ib = self.fields.iter().skip(1);
            let mut res = None;

            for (i, (a, b)) in ia.zip(ib).enumerate() {
                let off = align(a.offset + a.size, alignment);

                if off + size <= b.offset {
                    res = Some((off, i + 1));
                    break;
                }
            }

            res.or_else(|| {
                let last = self.fields.last().unwrap();
                Some((align(last.offset + last.size, alignment), self.fields.len()))
            }).unwrap()
        };

        if self.data.len() < offset + size {
            self.data.resize(offset + size, 0u8);
        }
        self.fields.insert(index, Field{
            key: k,
            offset: offset,
            size: size,
            id: id,
            tydesc: unsafe { get_tydesc::<T>() },
        });

        offset
    }

    /// Returns a pointer to `T` at the given offset.
    /// Does not perform any bounds checking.
    fn get_data<T: 'static>(&self, offset: usize) -> *const T {
        unsafe { self.data.as_ptr().offset(offset as isize) as *const T }
    }

    /// Returns a mutable pointer to `T` at the given offset.
    /// Does not perform any bounds checking.
    fn get_data_mut<T: 'static>(&mut self, offset: usize) -> *mut T {
        unsafe { self.data.as_mut_ptr().offset(offset as isize) as *mut T }
    }

    /// Returns a reference to the field descriptor for the given key.
    fn get_field<Q: ?Sized>(&self, k: &Q) -> Option<&Field<K>>
            where Q: Eq + BorrowFrom<K> {
        self.fields.iter().find(|f| k.eq(BorrowFrom::borrow_from(&f.key)))
    }

    /// Returns a reference to the field descriptor for the given key.
    ///
    /// # Panics
    ///
    /// If the given field has a different `TypeId` than the one given.
    fn get_field_with_id<Q: ?Sized>(&self, k: &Q, id: TypeId) -> Option<&Field<K>>
            where Q: Eq + BorrowFrom<K> {
        self.fields.iter().find(|f| {
            if k.eq(BorrowFrom::borrow_from(&f.key)) {
                if f.id != id {
                    panic!("lookup for value of a different type");
                }
                true
            } else {
                false
            }
        })
    }
}

#[unsafe_destructor]
impl<K: Eq> Drop for PolyMap<K> {
    fn drop(&mut self) {
        self.clear();
    }
}

/// Iterator over the keys of a `PolyMap`
#[derive(Clone)]
pub struct Keys<'a, K: 'a> {
    iter: Iter<'a, Field<K>>,
}

impl<'a, K> Iterator for Keys<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next().map(|f| &f.key)
    }
}

#[cfg(test)]
mod tests {
    use super::PolyMap;
    use std::sync::atomic::{AtomicUint, ATOMIC_UINT_INIT};
    use std::sync::atomic::Ordering::SeqCst;

    #[test]
    fn test_contains() {
        let mut map = PolyMap::new();

        map.insert("a", 1);
        assert!(map.contains_key("a"));
        assert!(!map.contains_key("b"));

        assert!(map.contains_key_of::<_, i32>("a"));
        assert!(!map.contains_key_of::<_, ()>("a"));
        assert!(!map.contains_key_of::<_, i32>("b"));
    }

    static DROP_COUNT: AtomicUint = ATOMIC_UINT_INIT;

    struct Dropper { n: usize }

    impl Drop for Dropper {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(self.n, SeqCst);
        }
    }

    #[test]
    fn test_drop() {
        DROP_COUNT.store(0, SeqCst);

        {
            let mut map = PolyMap::new();
            map.insert(0, Dropper{n: 1});
            map.insert(1, Dropper{n: 2});
            map.insert(2, Dropper{n: 3});
        }

        assert_eq!(DROP_COUNT.load(SeqCst), 6);
    }

    #[test]
    fn test_keys() {
        use std::collections::HashSet;

        let mut map = PolyMap::new();

        map.insert(0, 0xaa_u8);
        map.insert(1, 0xbb_u8);
        map.insert(2, 0xcc_u8);
        map.insert(3, 0xdd_u8);

        let keys: HashSet<u32> = map.keys().map(|i| *i).collect();
        assert_eq!(keys, vec![0, 1, 2, 3].into_iter().collect());
    }

    #[test]
    #[should_fail]
    fn test_mismatch_get() {
        let mut map = PolyMap::new();

        map.insert("a", 0xAAAAAAAA_u32);
        let _a: Option<&i32> = map.get("a");
    }

    #[test]
    #[should_fail]
    fn test_mismatch_insert() {
        let mut map = PolyMap::new();

        map.insert("a", 1i32);
        map.insert("a", 1u32);
    }

    #[test]
    #[should_fail]
    fn test_mismatch_remove() {
        let mut map = PolyMap::new();

        map.insert("a", 1);
        let _ = map.remove::<_, u32>("a");
    }

    #[test]
    fn test_packing() {
        let mut map = PolyMap::new();

        map.insert("a", 0xAA_u8);
        map.insert("b", 0xBBBB_u16);
        map.insert("c", 0xCC_u8);

        assert_eq!(map.get("a"), Some(&0xAA_u8));
        assert_eq!(map.get("b"), Some(&0xBBBB_u16));
        assert_eq!(map.get("c"), Some(&0xCC_u8));

        assert_eq!(map.data_size(), 4);

        let mut map = PolyMap::new();

        map.insert("a", 0xAAAA_u16);
        map.insert("b", 0xBBBBBBBB_u32);
        map.insert("c", 0xCC_u8);
        map.insert("d", 0xDD_u8);

        assert_eq!(map.get("a"), Some(&0xAAAA_u16));
        assert_eq!(map.get("b"), Some(&0xBBBBBBBB_u32));
        assert_eq!(map.get("c"), Some(&0xCC_u8));
        assert_eq!(map.get("d"), Some(&0xDD_u8));

        assert_eq!(map.data_size(), 8);
    }

    #[test]
    fn test_remove() {
        let mut map = PolyMap::new();

        map.insert("a", 0x87654321_u32);
        assert_eq!(map.remove("a"), Some(0x87654321_u32));
        assert_eq!(map.get::<_, u32>("a"), None);

        let b = "foo".to_string();
        map.insert("b", b);
        assert_eq!(map.get("b"), Some(&"foo".to_string()));

        let bb: String = map.remove("b").unwrap();
        assert_eq!(bb, "foo");
    }

    #[test]
    fn test_replace() {
        let mut map = PolyMap::new();

        map.insert("a", 0xAAAAAAAA_u32);
        assert_eq!(map.insert("a", 0xBBBBBBBB_u32), Some(0xAAAAAAAA_u32));
        assert_eq!(map.get("a"), Some(&0xBBBBBBBB_u32));

        map.insert("b", 0xCCCCCCCC_u32);
        assert_eq!(map.remove("b"), Some(0xCCCCCCCC_u32));
        assert_eq!(map.insert("c", 0xDDDDDDDDDDDDDDDD_u64), None);
    }

    #[test]
    fn test_reuse() {
        let mut map = PolyMap::new();

        map.insert("a", 0xAAAAAAAA_u32);
        map.insert("b", 0xBBBBBBBB_u32);

        assert_eq!(map.get("b"), Some(&0xBBBBBBBB_u32));
        assert_eq!(map.remove("a"), Some(0xAAAAAAAA_u32));

        map.insert("c", 0xCCCCCCCC_u32);

        assert_eq!(map.get("c"), Some(&0xCCCCCCCC_u32));
        assert_eq!(map.data_size(), 8);
    }

    #[test]
    fn test_insert() {
        let mut map = PolyMap::new();

        assert_eq!(map.insert("a", 0x12345678_u32), None);
        assert_eq!(map.insert("b", 0x12345678_u32), None);
        assert_eq!(map.get("a"), Some(&0x12345678_u32));
        assert_eq!(map.get("b"), Some(&0x12345678_u32));
        assert_eq!(map.get("c"), None::<&u32>);
    }

    #[test]
    fn test_strings() {
        let mut map = PolyMap::new();

        map.insert("a".to_string(), "a");
        map.insert("b".to_string(), "b");

        assert_eq!(map.get("a"), Some(&"a"));
        assert_eq!(map.get("b"), Some(&"b"));
    }

    #[derive(PartialEq, Eq, Show)]
    struct A;

    #[test]
    fn test_zero_size() {
        let mut map = PolyMap::new();

        map.insert("a", A);
        map.insert("b", A);
        map.insert("c", A);

        assert_eq!(map.get("a"), Some(&A));
        assert_eq!(map.get("b"), Some(&A));
        assert_eq!(map.get("c"), Some(&A));
        assert_eq!(map.data_size(), 0);
    }
}
