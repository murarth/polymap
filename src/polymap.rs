//! Provides the `PolyMap` implementation, mapping keys to heterogeneous values

use std::any::Any;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::{self, RandomState};
use std::hash::{BuildHasher, Hash};

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
