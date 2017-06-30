//! Mapping containers of heterogeneous values
//!
//! `polymap` provides implementations of two mapping containers for
//! heterogeneous values:
//!
//! * [`PolyMap`][polymap], which maps keys to values of varying type.
//! * [`TypeMap`][typemap], which stores values according to their type.
//!
//! [polymap]: polymap/struct.PolyMap.html
//! [typemap]: typemap/struct.TypeMap.html

#![deny(missing_docs)]

pub use polymap::PolyMap;
pub use typemap::TypeMap;

pub mod polymap;
pub mod typemap;
