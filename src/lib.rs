#![feature(core_intrinsics, vec_resize)]

//! `polymap` provides implementations of two mapping containers for
//! heterogeneous values:
//!
//! * [`PolyMap`](polymap/struct.PolyMap.html),
//!   which maps keys to values of varying type.
//! * [`TypeMap`](typemap/struct.TypeMap.html),
//!   which stores values according to their type.

pub use polymap::PolyMap;
pub use typemap::TypeMap;

pub mod polymap;
pub mod typemap;
