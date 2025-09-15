use std::collections::HashSet;

use red_black_tree::RedBlackTree;

fn main() {
    let mut set = HashSet::new();

    for i in 1..=15 {
        set.insert(i);
    }

    let tree: RedBlackTree<_> = set.into_iter().collect();

    println!("{tree:?}");
}