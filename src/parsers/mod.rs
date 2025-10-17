//! [`Parser`](super::Parser) implementations for common types defined as part of `kmdparse`
//!
//! Each parser in this module is designed to be as generic as is reasonable in order to allow the
//! crate's users to implement their own parser implementations on top of these built-in types.

#[cfg(feature = "std")]
mod paths;
mod primitives;
mod sequences;

#[cfg(feature = "std")]
pub use paths::*;
pub use primitives::*;
pub use sequences::*;
