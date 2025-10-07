use red_black_tree::{rbt, RedBlackTree};

fn main() {
    let tree = rbt!(i in 1..=15);
    println!("{tree:?}");
}