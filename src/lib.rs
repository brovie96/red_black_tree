//! A pair of basic safe [red-black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree) implementations.
/// Single-threaded version.
pub mod unsync;
/// Multi-threaded version.
pub mod sync;

/// A helper macro for creating red-black trees from arbitrary data.
///
/// There are two forms of this macro:
/// - Create a red-black tree from a list of elements:
/// ```
/// use red_black_tree::{rbt, unsync::RedBlackTree};
/// let tree = rbt![1, 2, 3];
/// assert!(tree.contains(1));
/// assert!(tree.contains(2));
/// assert!(tree.contains(3));
/// ```
/// - Create a red-black tree from an iterator:
/// ```
/// use red_black_tree::{rbt, unsync::RedBlackTree};
/// let tree = rbt!(i in 1..=15);
/// for i in 1..=15 {
///     assert!(tree.contains(i));
/// }
/// ```
#[macro_export]
macro_rules! rbt {
    ($($e:expr),*) => {
        rbt!(i in vec![$($e),*].into_iter())
    };
    ($i:ident in $e:expr) => {{
        $e.collect::<RedBlackTree<_>>()
    }};
}