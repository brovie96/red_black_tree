use red_black_tree::RedBlackTree;
use red_black_tree::rbt;

fn main() {
    let tree = rbt!(i in 1..=15);
    println!("{tree:?}");
}