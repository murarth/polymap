//! Provides the `PolyMap` implementation, mapping keys to heterogeneous values

use std::any::Any;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::{self, RandomState};
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

/// A key-value map that can contain varying types of values.
///
/// A single `PolyMap` instance can map a given key to varying types of values.
/// Successive operations on this key must use the correct type or the operation
/// will panic.
///
/// If you would like to store only one value of each type,
/// use [`TypeMap`](../typemap/struct.TypeMap.html).
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
/// let &foo: &&str = map.get("foo").unwrap();
/// assert_eq!(foo, "Hello, world!");
///
/// let &bar: &i32 = map.get("bar").unwrap();
/// assert_eq!(bar, 123);
/// ```
pub struct PolyMap<K: Eq + Hash, S = RandomState> {
    map: HashMap<K, Box<Any>, S>,
}

impl<K: Eq + Hash> PolyMap<K, RandomState> {
    /// Constructs a new `PolyMap`.
    pub fn new() -> PolyMap<K> {
        PolyMap{
            map: HashMap::new(),
        }
    }

    /// Constructs a new `PolyMap` with space reserved for `n` elements.
    pub fn with_capacity(n: usize) -> PolyMap<K> {
        PolyMap{
            map: HashMap::with_capacity(n),
        }
    }
}

impl<K: Eq + Hash, S: BuildHasher> PolyMap<K, S> {
    /// Creates an empty `PolyMap` which will use the given hash builder to hash keys.
    pub fn with_hasher(hash_builder: S) -> PolyMap<K, S> {
        PolyMap{
            map: HashMap::with_hasher(hash_builder),
        }
    }

    /// Removes all key-value pairs from the map.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns whether the map contains a value corresponding to the given key.
    /// Does not make any assertions about the type of the value.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
            where K: Borrow<Q>, Q: Eq + Hash {
        self.map.contains_key(k)
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
    pub fn contains_key_of<Q: ?Sized, T: Any>(&self, k: &Q) -> bool
            where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get(k).map_or(false, |v| v.is::<T>())
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Returns the key's corresponding entry in the map for in-place manipulation.
    ///
    /// Whether the entry is occupied or vacant, the type of value that can be
    /// inserted into the returned entry is constrained to `T`.
    ///
    /// # Panics
    ///
    /// If the entry exists, but the type of value differs from the one requested.
    pub fn entry<T: Any>(&mut self, key: K) -> Entry<K, T> {
        match self.map.entry(key) {
            hash_map::Entry::Vacant(ent) => Entry::Vacant(VacantEntry::new(ent)),
            hash_map::Entry::Occupied(ent) => {
                if !ent.get().is::<T>() {
                    panic!("entry for value of a different type");
                }

                Entry::Occupied(OccupiedEntry::new(ent))
            }
        }
    }

    /// Returns a reference to the value corresponding to the given key.
    ///
    /// If the key is not contained within the map, `None` will be returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn get<Q: ?Sized, T: Any>(&self, k: &Q) -> Option<&T>
            where K: Borrow<Q>, Q: Eq + Hash {
        if let Some(v) = self.map.get(k) {
            if let Some(v) = v.downcast_ref() {
                Some(v)
            } else {
                panic!("lookup for value of a different type");
            }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the given key.
    ///
    /// If the key is not contained within the map, `None` will be returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn get_mut<Q: ?Sized, T: Any>(&mut self, k: &Q) -> Option<&mut T>
            where K: Borrow<Q>, Q: Eq + Hash {
        if let Some(v) = self.map.get_mut(k) {
            if let Some(v) = v.downcast_mut() {
                Some(v)
            } else {
                panic!("lookup for value of a different type");
            }
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the map. If the key is already present,
    /// that value is returned. Otherwise, `None` is returned.
    ///
    /// # Panics
    ///
    /// If the key exists, but has a value of a different type than the one given.
    pub fn insert<T: Any>(&mut self, k: K, t: T) -> Option<T> {
        let old = self.map.insert(k, Box::new(t));

        if let Some(v) = old {
            if let Ok(v) = v.downcast() {
                Some(*v)
            } else {
                panic!("insert value of different type");
            }
        } else {
            None
        }
    }

    /// Returns an iterator visiting all keys in arbitrary order.
    /// Iterator element type is `&K`.
    pub fn keys(&self) -> Keys<K> {
        Keys{iter: self.map.keys()}
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Reserves capacity for at least `additional` additional elements.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
    }

    /// Removes a key from the map, returning the value if one existed.
    ///
    /// # Panics
    ///
    /// If the key exists, but the type of value differs from the one requested.
    pub fn remove<Q: ?Sized, T: Any>(&mut self, k: &Q) -> Option<T>
            where K: Borrow<Q>, Q: Eq + Hash {
        let v = self.map.remove(k);

        if let Some(v) = v {
            if let Ok(v) = v.downcast() {
                Some(*v)
            } else {
                panic!("remove value of different type");
            }
        } else {
            None
        }
    }

    /// Shrinks the capacity of the map as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }
}

impl<K: Eq + Hash, S: BuildHasher + Default> Default for PolyMap<K, S> {
    fn default() -> PolyMap<K, S> {
        PolyMap::with_hasher(S::default())
    }
}

/// A view into a single entry in a map, which may be either vacant or occupied.
///
/// This enum is returned from the [`entry`][entry] method on [`PolyMap`][polymap].
///
/// [polymap]: struct.PolyMap.html
/// [entry]: struct.PolyMap.html#method.entry
pub enum Entry<'a, K: 'a, V: Any> {
    /// An occupied entry
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V: Any> Entry<'a, K, V> {
    /// Inserts a value if empty, then returns a mutable reference.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(ent) => ent.into_mut(),
            Entry::Vacant(ent) => ent.insert(default)
        }
    }

    /// Inserts a value if empty using the given function,
    /// then returns a mutable reference.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(ent) => ent.into_mut(),
            Entry::Vacant(ent) => ent.insert(default())
        }
    }

    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref ent) => ent.key(),
            Entry::Vacant(ref ent) => ent.key()
        }
    }
}

impl<'a, K: 'a + fmt::Debug, V: Any + fmt::Debug> fmt::Debug for Entry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Entry::Occupied(ref ent) =>
                f.debug_tuple("Entry")
                    .field(ent)
                    .finish(),
            Entry::Vacant(ref ent) =>
                f.debug_tuple("Entry")
                    .field(ent)
                    .finish(),
        }
    }
}

/// A view into an occupied entry in a `PolyMap`.
pub struct OccupiedEntry<'a, K: 'a, V: Any> {
    entry: hash_map::OccupiedEntry<'a, K, Box<Any>>,
    _data: PhantomData<V>,
}

impl<'a, K, V: Any> OccupiedEntry<'a, K, V> {
    fn new(entry: hash_map::OccupiedEntry<'a, K, Box<Any>>) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry{
            entry: entry,
            _data: PhantomData,
        }
    }

    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    /// Removes the entry and returns its key value pair.
    pub fn remove_entry(self) -> (K, V) {
        let (k, v) = self.entry.remove_entry();
        (k, *v.downcast().expect("wrong type in entry"))
    }

    /// Returns a reference to the entry value.
    pub fn get(&self) -> &V {
        self.entry.get().downcast_ref().expect("wrong type in entry")
    }

    /// Returns a mutable reference to the entry value.
    pub fn get_mut(&mut self) -> &mut V {
        self.entry.get_mut().downcast_mut().expect("wrong type in entry")
    }

    /// Consumes the entry and returns a mutable reference
    /// tied to the lifetime of the parent container.
    pub fn into_mut(self) -> &'a mut V {
        self.entry.into_mut().downcast_mut().expect("wrong type in entry")
    }

    /// Inserts a value into the entry and returns the old value.
    pub fn insert(&mut self, value: V) -> V {
        *self.entry.insert(Box::new(value)).downcast().expect("wrong type in entry")
    }

    /// Removes the entry and returns the value.
    pub fn remove(self) -> V {
        *self.entry.remove().downcast().expect("wrong type in entry")
    }
}

impl<'a, K: fmt::Debug, V: Any + fmt::Debug> fmt::Debug for OccupiedEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

/// A view into a vacant entry in a `PolyMap`.
pub struct VacantEntry<'a, K: 'a, V: Any> {
    entry: hash_map::VacantEntry<'a, K, Box<Any>>,
    _data: PhantomData<V>,
}

impl<'a, K: 'a, V: Any> VacantEntry<'a, K, V> {
    fn new(entry: hash_map::VacantEntry<'a, K, Box<Any>>) -> VacantEntry<'a, K, V> {
        VacantEntry{
            entry: entry,
            _data: PhantomData,
        }
    }

    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    /// Consumes the entry and returns the owned key value.
    pub fn into_key(self) -> K {
        self.entry.into_key()
    }

    /// Consumes the entry, inserting a value and returning a mutable reference.
    pub fn insert(self, value: V) -> &'a mut V {
        self.entry.insert(Box::new(value)).downcast_mut().expect("wrong type in entry")
    }
}

impl<'a, K: fmt::Debug, V: Any> fmt::Debug for VacantEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("VacantEntry")
            .field("key", self.key())
            .finish()
    }
}

/// Iterator over the keys of a `PolyMap`
#[derive(Clone)]
pub struct Keys<'a, K: 'a> {
    iter: hash_map::Keys<'a, K, Box<Any>>
}

impl<'a, K> Iterator for Keys<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next()
    }
}

#[cfg(test)]
mod test {
    use super::PolyMap;
    use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT};
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

    #[test]
    fn test_entry() {
        let mut m = PolyMap::new();

        m.entry("foo").or_insert(123u32);
        m.entry("bar").or_insert_with(String::new);

        assert_eq!(m.len(), 2);
        assert_eq!(m.get::<_, u32>("foo"), Some(&123));
        assert_eq!(m.get::<_, String>("bar"), Some(&String::new()));
    }

    #[test]
    #[should_panic]
    fn test_entry_fail() {
        let mut m = PolyMap::new();

        m.insert("foo", 123);

        let _ = m.entry::<String>("foo");
    }

    static DROP_COUNT: AtomicUsize = ATOMIC_USIZE_INIT;

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
    #[should_panic]
    fn test_mismatch_get() {
        let mut map = PolyMap::new();

        map.insert("a", 0xAAAAAAAA_u32);
        let _a: Option<&i32> = map.get("a");
    }

    #[test]
    #[should_panic]
    fn test_mismatch_insert() {
        let mut map = PolyMap::new();

        map.insert("a", 1i32);
        map.insert("a", 1u32);
    }

    #[test]
    #[should_panic]
    fn test_mismatch_remove() {
        let mut map = PolyMap::new();

        map.insert("a", 1);
        let _ = map.remove::<_, u32>("a");
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

        map.insert("a".to_string(), "a".to_string());
        map.insert("b".to_string(), "b".to_string());

        assert_eq!(map.get::<_, String>("a"), Some(&"a".to_string()));
        assert_eq!(map.get::<_, String>("b"), Some(&"b".to_string()));
    }
}
