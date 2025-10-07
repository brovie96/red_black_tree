//! A pair of basic safe [red-black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree) implementations.
/// Single-threaded version.
pub mod unsync;
/// Multi-threaded version.
pub mod sync;