//! Provides the `TypeMap` implementation, mapping types to values

use std::any::{Any, TypeId};
use std::collections::hash_map::RandomState;
use std::hash::BuildHasher;

use polymap::PolyMap;

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
    map: PolyMap<TypeId, S>,
}

impl TypeMap<RandomState> {
    /// Constructs a new `TypeMap`.
    pub fn new() -> TypeMap {
        TypeMap{map: PolyMap::new()}
    }

    /// Constructs a new `PolyMap` with space reserved for `n` elements.
    pub fn with_capacity(n: usize) -> TypeMap {
        TypeMap{map: PolyMap::with_capacity(n)}
    }
}

impl<S: BuildHasher> TypeMap<S> {
    /// Creates an empty `TypeMap` which will use the given hash builder to hash keys.
    pub fn with_hasher(hash_builder: S) -> TypeMap<S> {
        TypeMap{
            map: PolyMap::with_hasher(hash_builder),
        }
    }

    /// Removes all key-value pairs from the map.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns whether the map contains a value of the given type.
    pub fn contains<T: Any>(&self) -> bool {
        self.map.contains_key(&TypeId::of::<T>())
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Returns a reference to the value of the given type.
    ///
    /// If no value of the given type exists, `None` is returned.
    pub fn get<T: Any>(&self) -> Option<&T> {
        self.map.get(&TypeId::of::<T>())
    }

    /// Returns a mutable reference to the value of the given type.
    ///
    /// If no value of the given type exists, `None` is returned.
    pub fn get_mut<T: Any>(&mut self) -> Option<&mut T> {
        self.map.get_mut(&TypeId::of::<T>())
    }

    /// Inserts a value into the map. If a value of the same type is
    /// already present, that value is returned. Otherwise, `None` is returned.
    pub fn insert<T: Any>(&mut self, t: T) -> Option<T> {
        self.map.insert(TypeId::of::<T>(), t)
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Removes a value of the given type from the map, returning it.
    /// If no value of the type exists, `None` is returned.
    pub fn remove<T: Any>(&mut self) -> Option<T> {
        self.map.remove(&TypeId::of::<T>())
    }

    /// Reserves capacity for at least `additional` additional elements.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
    }

    /// Shrinks the capacity of the map as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }
}

impl<S: BuildHasher + Default> Default for TypeMap<S> {
    fn default() -> TypeMap<S> {
        TypeMap::with_hasher(S::default())
    }
}

#[cfg(test)]
mod test {
    use super::TypeMap;

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
