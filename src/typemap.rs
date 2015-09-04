use std::any::{Any, TypeId};

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
///
/// # Notes
///
/// Values are stored in an internal buffer that is reallocated when filled.
/// Methods `reserve_data`, `reserve_data_exact`, and constructor `with_capacity`
/// can be used to reserve a larger buffer ahead of time to prevent expensive
/// reallocation and move operations.
#[derive(Default)]
pub struct TypeMap {
    map: PolyMap<TypeId>,
}

impl TypeMap {
    /// Constructs a new `TypeMap`.
    pub fn new() -> TypeMap {
        TypeMap{map: PolyMap::new()}
    }

    /// Constructs a new `PolyMap` with space reserved for `n` fields
    /// and `size` bytes of data.
    pub fn with_capacity(n: usize, size: usize) -> TypeMap {
        TypeMap{map: PolyMap::with_capacity(n, size)}
    }

    /// Removes all key-value pairs from the map, calling any destructors on
    /// stored values.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns whether the map contains a value of the given type.
    pub fn contains<T: Any>(&self) -> bool {
        self.map.contains_key(&TypeId::of::<T>())
    }

    /// Returns the capacity, in bytes, of the internal data buffer.
    pub fn data_capacity(&self) -> usize {
        self.map.data_capacity()
    }

    /// Returns the size, in bytes, of the internal data buffer.
    pub fn data_size(&self) -> usize {
        self.map.data_size()
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

    /// Removes a value of the given type from the map, returning it.
    /// If no value of the type exists, `None` is returned.
    pub fn remove<T: Any>(&mut self) -> Option<T> {
        self.map.remove(&TypeId::of::<T>())
    }

    /// Reserves capacity for at least `additional` additional bytes of storage
    /// space within the internal data buffer.
    pub fn reserve_data(&mut self, additional: usize) {
        self.map.reserve_data(additional);
    }

    /// Reserves space for at least `n` bytes in the internal data buffer.
    /// Does nothing if the capacity is already sufficient.
    pub fn reserve_data_exact(&mut self, additional: usize) {
        self.map.reserve_data_exact(additional);
    }

    /// Reserves capacity for at least `additional` additional fields.
    pub fn reserve_fields(&mut self, additional: usize) {
        self.map.reserve_fields(additional);
    }

    /// Reserves space for at least `n` fields.
    /// Does nothing if the capacity is already sufficient.
    pub fn reserve_fields_exact(&mut self, additional: usize) {
        self.map.reserve_fields_exact(additional);
    }

    /// Shrinks the internal data buffer as close as possible to the size of
    /// the currently contained elements.
    pub fn shrink_data_to_fit(&mut self) {
        self.map.shrink_data_to_fit();
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
