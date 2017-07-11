//! Provides the `TypeMap` implementation, mapping types to values

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::collections::hash_map::{self, RandomState};
use std::fmt;
use std::hash::BuildHasher;
use std::marker::PhantomData;

/// A container for values of varying types.
///
/// Values contained in a `TypeMap` are stored uniquely according to their type.
/// This means that, for each possible type, only one value may be stored in
/// a single `TypeMap` instance.
///
/// If you would like to store multiple values of a given type, mapped to
/// individual keys, use [`PolyMap`](../polymap/struct.PolyMap.html).
///
/// # Example
///
/// ```
/// use polymap::TypeMap;
///
/// let mut map = TypeMap::new();
///
/// // Stores a `&str` value
/// map.insert("Hello, world!");
///
/// // Stores an `i32` value
/// map.insert(123);
///
/// // Gets a reference to the stored value
/// let &foo: &&str = map.get().unwrap();
/// assert_eq!(foo, "Hello, world!");
///
/// let &bar: &i32 = map.get().unwrap();
/// assert_eq!(bar, 123);
/// ```
pub struct TypeMap<S = RandomState> {
    map: HashMap<TypeId, Box<Any>, S>,
}

impl TypeMap<RandomState> {
    /// Constructs a new `TypeMap`.
    #[inline]
    pub fn new() -> TypeMap {
        TypeMap{
            map: HashMap::new(),
        }
    }

    /// Constructs a new `TypeMap` with space reserved for `n` elements.
    #[inline]
    pub fn with_capacity(n: usize) -> TypeMap {
        TypeMap{
            map: HashMap::with_capacity(n),
        }
    }
}

impl<S: BuildHasher> TypeMap<S> {
    /// Creates an empty `TypeMap` which will use the given hash builder to hash keys.
    #[inline]
    pub fn with_hasher(hash_builder: S) -> TypeMap<S> {
        TypeMap{
            map: HashMap::with_hasher(hash_builder),
        }
    }

    /// Removes all values from the map.
    #[inline]
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns whether the map contains a value corresponding to the given type.
    #[inline]
    pub fn contains<T: Any>(&self) -> bool {
        self.map.contains_key(&TypeId::of::<T>())
    }

    /// Returns the number of elements the map can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Returns the type's corresponding entry in the map for in-place manipulation.
    #[inline]
    pub fn entry<T: Any>(&mut self) -> Entry<T> {
        match self.map.entry(TypeId::of::<T>()) {
            hash_map::Entry::Vacant(ent) => Entry::Vacant(VacantEntry::new(ent)),
            hash_map::Entry::Occupied(ent) => Entry::Occupied(OccupiedEntry::new(ent))
        }
    }

    /// Returns a reference to the value corresponding to the given type.
    ///
    /// If the type is not contained within the map, `None` will be returned.
    #[inline]
    pub fn get<T: Any>(&self) -> Option<&T> {
        if let Some(v) = self.map.get(&TypeId::of::<T>()) {
            Some(v.downcast_ref().expect("wrong type in TypeMap"))
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the given type.
    ///
    /// If the type is not contained within the map, `None` will be returned.
    #[inline]
    pub fn get_mut<T: Any>(&mut self) -> Option<&mut T> {
        if let Some(v) = self.map.get_mut(&TypeId::of::<T>()) {
            Some(v.downcast_mut().expect("wrong type in TypeMap"))
        } else {
            None
        }
    }

    /// Inserts a value into the map. If a value of that type is already present,
    /// that value is returned. Otherwise, `None` is returned.
    #[inline]
    pub fn insert<T: Any>(&mut self, t: T) -> Option<T> {
        self.map.insert(TypeId::of::<T>(), Box::new(t))
            .map(|old| *old.downcast().expect("wrong type in TypeMap"))
    }

    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns whether the map is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Reserves capacity for at least `additional` additional elements.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
    }

    /// Removes a value from the map, returning the value if one existed.
    #[inline]
    pub fn remove<T: Any>(&mut self) -> Option<T> {
        self.map.remove(&TypeId::of::<T>())
            .map(|old| *old.downcast().expect("wrong type in TypeMap"))
    }

    /// Shrinks the capacity of the map as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }
}

impl<S> fmt::Debug for TypeMap<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("TypeMap { .. }")
    }
}

impl<S: BuildHasher + Default> Default for TypeMap<S> {
    fn default() -> TypeMap<S> {
        TypeMap::with_hasher(S::default())
    }
}

/// A view into a single entry in a map, which may be either vacant or occupied.
///
/// This enum is returned from the [`entry`][entry] method on [`TypeMap`][typemap].
///
/// [typemap]: struct.TypeMap.html
/// [entry]: struct.TypeMap.html#method.entry
pub enum Entry<'a, V: Any> {
    /// An occupied entry
    Occupied(OccupiedEntry<'a, V>),
    /// A vacant entry
    Vacant(VacantEntry<'a, V>),
}

impl<'a, V: Any> Entry<'a, V> {
    /// Inserts a value if empty, then returns a mutable reference.
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(ent) => ent.into_mut(),
            Entry::Vacant(ent) => ent.insert(default)
        }
    }

    /// Inserts a value if empty using the given function,
    /// then returns a mutable reference.
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(ent) => ent.into_mut(),
            Entry::Vacant(ent) => ent.insert(default())
        }
    }
}

impl<'a, V: Any + fmt::Debug> fmt::Debug for Entry<'a, V> {
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

/// A view into an occupied entry in a `TypeMap`.
pub struct OccupiedEntry<'a, V: Any> {
    entry: hash_map::OccupiedEntry<'a, TypeId, Box<Any>>,
    _data: PhantomData<V>,
}

impl<'a, V: Any> OccupiedEntry<'a, V> {
    fn new(entry: hash_map::OccupiedEntry<'a, TypeId, Box<Any>>) -> OccupiedEntry<'a, V> {
        OccupiedEntry{
            entry: entry,
            _data: PhantomData,
        }
    }

    /// Returns a reference to the entry value.
    #[inline]
    pub fn get(&self) -> &V {
        self.entry.get().downcast_ref().expect("wrong type in entry")
    }

    /// Returns a mutable reference to the entry value.
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.entry.get_mut().downcast_mut().expect("wrong type in entry")
    }

    /// Consumes the entry and returns a mutable reference
    /// tied to the lifetime of the parent container.
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.entry.into_mut().downcast_mut().expect("wrong type in entry")
    }

    /// Inserts a value into the entry and returns the old value.
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        *self.entry.insert(Box::new(value)).downcast().expect("wrong type in entry")
    }

    /// Removes the entry and returns the value.
    #[inline]
    pub fn remove(self) -> V {
        *self.entry.remove().downcast().expect("wrong type in entry")
    }
}

impl<'a, V: Any + fmt::Debug> fmt::Debug for OccupiedEntry<'a, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("OccupiedEntry")
            .field(self.get())
            .finish()
    }
}

/// A view into a vacant entry in a `TypeMap`.
pub struct VacantEntry<'a, V: Any> {
    entry: hash_map::VacantEntry<'a, TypeId, Box<Any>>,
    _data: PhantomData<V>,
}

impl<'a, V: Any> VacantEntry<'a, V> {
    fn new(entry: hash_map::VacantEntry<'a, TypeId, Box<Any>>) -> VacantEntry<'a, V> {
        VacantEntry{
            entry: entry,
            _data: PhantomData,
        }
    }

    /// Consumes the entry, inserting a value and returning a mutable reference.
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        self.entry.insert(Box::new(value)).downcast_mut().expect("wrong type in entry")
    }
}

impl<'a, V: Any> fmt::Debug for VacantEntry<'a, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("VacantEntry { .. }")
    }
}

#[cfg(test)]
mod test {
    use super::TypeMap;

    #[test]
    fn test_debug() {
        let mut m = TypeMap::new();

        m.insert(123_i32);

        assert_eq!(format!("{:?}", m), "TypeMap { .. }");

        assert_eq!(format!("{:?}", m.entry::<i32>()),
            r#"Entry(OccupiedEntry(123))"#);
        assert_eq!(format!("{:?}", m.entry::<()>()),
            r#"Entry(VacantEntry { .. })"#);
    }

    #[test]
    fn test_entry() {
        let mut m = TypeMap::new();

        m.entry::<u32>().or_insert(123);
        m.entry::<String>().or_insert_with(String::new);

        assert_eq!(m.len(), 2);
        assert_eq!(m.get::<u32>(), Some(&123));
        assert_eq!(m.get::<String>(), Some(&String::new()));
    }

    #[derive(Debug, Eq, PartialEq)]
    struct Foo {
        a: i32,
        b: i32,
    }

    #[test]
    fn test_typemap() {
        let mut m = TypeMap::new();

        m.insert(123);
        m.insert(456_u32);
        m.insert("foo");
        m.insert(Foo{a: 1, b: 2});

        assert_eq!(m.get::<i32>(), Some(&123));
        assert_eq!(m.get::<u32>(), Some(&456));
        assert_eq!(m.get::<&str>(), Some(&"foo"));
        assert_eq!(m.get::<Foo>(), Some(&Foo{a: 1, b: 2}));
    }
}
