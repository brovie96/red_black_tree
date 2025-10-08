use std::sync::{Arc, Mutex};
use rayon::prelude::*;
use red_black_tree::sync::RedBlackTree;

fn main() {
    let tree = Arc::new(Mutex::new(RedBlackTree::new()));

    (1..=30).into_par_iter().for_each(|i| {
        tree.lock().unwrap().insert(i);
    });

    println!("{tree:?}");
}