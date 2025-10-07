use std::sync::{Arc, RwLock, Weak};

/// A basic safe multi-threaded [red-black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree) implementation.
/// # Example
/// ```
/// use red_black_tree::sync::RedBlackTree;
///
/// let mut tree = RedBlackTree::new();
/// assert_eq!(tree.insert(5), true);
/// assert_eq!(tree.insert(8), true);
/// // repeat inserts return false
/// assert_eq!(tree.insert(5), false);
///
/// assert_eq!(tree.contains(5), true);
/// assert_eq!(tree.contains(8), true);
/// assert_eq!(tree.contains(6), false);
///
/// assert_eq!(tree.remove(5), true);
/// assert_eq!(tree.contains(5), false);
/// // .remove() on an element not in the tree returns false
/// assert_eq!(tree.remove(6), false);
/// ```
#[derive(Debug)]
pub struct RedBlackTree<T: Clone + Ord> {
    root: Link<T>,
    size: usize,
}

type Link<T> = Option<Arc<RwLock<Node<T>>>>;
type RefLink<'a, T> = Option<&'a Arc<RwLock<Node<T>>>>;
type WeakLink<T> = Option<Weak<RwLock<Node<T>>>>;

#[derive(Debug)]
struct Node<T: Clone + Ord> {
    val: T,
    color: Color,
    parent: WeakLink<T>,
    left: Link<T>,
    right: Link<T>
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

#[derive(Clone, Copy)]
enum Direction {
    Left,
    Right
}

impl Direction {
    fn opposite(&self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

impl<T: Clone + Ord> Node<T> {
    fn new(val: T) -> Link<T> {
        // new nodes are red by default
        Some(Arc::new(RwLock::new(Self { val, color: Color::Red, parent: None, left: None, right: None })))
    }

    fn direction(this: RefLink<T>) -> Option<Direction> {
        this.unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade()).map(|parent|
            if parent.read().unwrap().right.is_some() && Arc::ptr_eq(this.unwrap(), parent.read().unwrap().right.as_ref().unwrap()) {
                Direction::Right
            } else {
                Direction::Left
            })
    }

    fn is_leaf(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }
}

impl<T: Clone + Ord> RedBlackTree<T> {
    /// Creates a new empty tree.
    pub fn new() -> Self {
        Self { root: None, size: 0 }
    }

    /// Returns the number of elements in the tree.
    /// # Examples
    ///
    /// A newly-created tree has a size of 0:
    ///
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// let mut tree = RedBlackTree::new();
    /// assert_eq!(tree.size(), 0);
    /// # tree.insert(5);
    /// # assert_eq!(tree.size(), 1);
    /// # tree.insert(8);
    /// # assert_eq!(tree.size(), 2);
    /// # tree.remove(5);
    /// # assert_eq!(tree.size(), 1);
    /// ```
    ///
    /// Adding elements increases the size:
    ///
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// # let mut tree = RedBlackTree::new();
    /// # assert_eq!(tree.size(), 0);
    /// tree.insert(5);
    /// assert_eq!(tree.size(), 1);
    /// tree.insert(8);
    /// assert_eq!(tree.size(), 2);
    /// # tree.remove(5);
    /// # assert_eq!(tree.size(), 1);
    /// ```
    ///
    /// Removing elements decreases the size:
    ///
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// # let mut tree = RedBlackTree::new();
    /// # assert_eq!(tree.size(), 0);
    /// # tree.insert(5);
    /// # assert_eq!(tree.size(), 1);
    /// # tree.insert(8);
    /// # assert_eq!(tree.size(), 2);
    /// tree.remove(5);
    /// assert_eq!(tree.size(), 1);
    /// ```
    pub fn size(&self) -> usize {
        self.size
    }

    /// Inserts a value into the tree if it is not already present. Returns whether the value was not already in the tree.
    /// # Example
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// let mut tree = RedBlackTree::new();
    /// assert_eq!(tree.insert(5), true);
    /// assert_eq!(tree.insert(8), true);
    /// // repeat inserts return false
    /// assert_eq!(tree.insert(5), false);
    /// ```
    pub fn insert(&mut self, val: T) -> bool {
        // generate new node with val
        let new_node = Node::new(val.clone());

        // if root is null, recolor node to black and set it as the root
        if self.root.is_none() {
            self.root = new_node;
            self.root.as_ref().unwrap().write().unwrap().color = Color::Black;
            self.size += 1;
            return true;
        }

        // insert node if the value is not already in the tree
        if let Err((parent_node, insert_direction)) = self.find_target_node(val) {
            new_node.as_ref().unwrap().write().unwrap().parent = Some(Arc::downgrade(parent_node.as_ref().unwrap()));
            match insert_direction {
                Direction::Left => parent_node.as_ref().unwrap().write().unwrap().left = new_node.clone(),
                Direction::Right => parent_node.as_ref().unwrap().write().unwrap().right = new_node.clone(),
            }
            // rebalance the tree
            self.rebalance_at_point(new_node);
            self.size += 1;
            true
        } else {
            false
        }
    }

    /// Returns whether the given val is present in the tree.
    /// # Example
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// let mut tree = RedBlackTree::new();
    /// tree.insert(5);
    /// assert_eq!(tree.contains(5), true);
    /// // returns false for a value not in the tree
    /// assert_eq!(tree.contains(8), false);
    /// ```
    pub fn contains(&self, val: T) -> bool {
        // if root is None, the tree is empty; always return false
        if self.root.is_none() {
            return false;
        }
        // look for target node and return whether it is some
        self.find_target_node(val).is_ok()
    }

    /// Removes a value from the tree if it exists.
    /// Returns whether the value was in the tree.
    /// # Example
    /// ```
    /// # use red_black_tree::sync::RedBlackTree;
    /// #
    /// let mut tree = RedBlackTree::new();
    /// tree.insert(5);
    /// // .remove() on an element in the tree returns true
    /// assert_eq!(tree.remove(5), true);
    /// // .contains() will now return false
    /// assert_eq!(tree.contains(5), false);
    /// // .remove() on an element not in the tree returns false
    /// assert_eq!(tree.remove(6), false);
    /// ```
    pub fn remove(&mut self, val: T) -> bool {
        // if tree is empty, there is nothing to do
        if self.root.is_none() {
            return false;
        }

        // get node to remove, and return false if it is none
        let mut removal_node = if let Ok(node) = self.find_target_node(val) {
            node
        } else {
            return false;
        };

        // decrement size since we are doing a removal if we got here
        self.size -= 1;

        // removal_node now contains the node with the value to remove; follow removal steps
        while !removal_node.as_ref().unwrap().read().unwrap().is_leaf() {
            // get nearest value, preferring next largest, and swap removal_node to that position,
            // swapping the value into the position currently occupied by removal_node
            if removal_node.as_ref().unwrap().read().unwrap().right.is_some() {
                let mut right_subtree_min = removal_node.as_ref().unwrap().read().unwrap().right.clone();

                while right_subtree_min.as_ref().unwrap().read().unwrap().left.is_some() {
                    right_subtree_min = right_subtree_min.take().unwrap().read().unwrap().left.clone();
                }

                removal_node.as_ref().unwrap().write().unwrap().val = right_subtree_min.as_ref().unwrap().read().unwrap().val.clone();
                removal_node = right_subtree_min;
            } else {
                let mut left_subtree_max = removal_node.as_ref().unwrap().read().unwrap().left.clone();

                while left_subtree_max.as_ref().unwrap().read().unwrap().right.is_some() {
                    left_subtree_max = left_subtree_max.take().unwrap().read().unwrap().right.clone();
                }

                removal_node.as_ref().unwrap().write().unwrap().val = left_subtree_max.as_ref().unwrap().read().unwrap().val.clone();
                removal_node = left_subtree_max;
            }
        }

        // we are down to a leaf node; remove it
        // if removal node is root, it is the last element in the tree;
        // unassign root and we're done
        if Arc::ptr_eq(removal_node.as_ref().unwrap(), self.root.as_ref().unwrap()) {
            self.root = None;
            return true;
        }
        let parent = removal_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|node| node.upgrade());
        let removal_node_direction = Node::direction(removal_node.as_ref());
        match removal_node_direction.as_ref().unwrap() {
            Direction::Left => parent.as_ref().unwrap().write().unwrap().left = None,
            Direction::Right => parent.as_ref().unwrap().write().unwrap().right = None,
        }

        if removal_node.as_ref().unwrap().read().unwrap().color == Color::Black {
            // removal_node is now double-black, follow steps to repair tree constraints
            self.resolve_double_black(removal_node, removal_node_direction);
        } // skipping this block is case 1

        true
    }

    // returns the node with the target value if it is in the tree
    // otherwise returns the insertion point (parent and direction)
    fn find_target_node(&self, target: T) -> Result<Link<T>, (Link<T>, Direction)> {
        // walk down tree to look for the node with target in it
        let mut cur_node = self.root.clone();

        loop {
            if cur_node.as_ref().unwrap().read().unwrap().val == target {
                // found it!
                return Ok(cur_node);
            } else {
                // continue down to the children
                let direction = if target < cur_node.as_ref().unwrap().read().unwrap().val {
                    Direction::Left
                } else {
                    Direction::Right
                };
                if let Some(child) = Self::check_child(cur_node.as_ref(), direction) {
                    // if the child is Some, continue searching
                    cur_node = child;
                } else {
                    // if the child is None, target is not in the tree
                    return Err((cur_node, direction))
                }
            }
        }
    }

    // checks child in the given direction and returns it if it's some
    fn check_child(node: RefLink<T>, direction: Direction) -> Option<Link<T>> {
        match direction {
            Direction::Left => node.unwrap().read().unwrap().left.clone(),
            Direction::Right => node.unwrap().read().unwrap().right.clone(),
        }.map(Some)
    }

    fn resolve_double_black(&mut self, db_node: Link<T>, db_direction: Option<Direction>) {
        // easiest case (if db is root, we're done)
        if Arc::ptr_eq(db_node.as_ref().unwrap(), self.root.as_ref().unwrap()) {
            // case 2
            return;
        }

        let db_direction = db_direction.or_else(|| Node::direction(db_node.as_ref())).unwrap();

        // implement other cases
        let sibling = match db_direction {
            Direction::Left => db_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade()).as_ref().unwrap().read().unwrap().right.clone(),
            Direction::Right => db_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade()).as_ref().unwrap().read().unwrap().left.clone(),
        };
        // assume the sibling is always Some (this better not bite me in the ass)
        let sibling_color = sibling.as_ref().unwrap().read().unwrap().color;
        match sibling_color {
            Color::Black => {
                let (sibling_near_child_color, sibling_far_child_color) = match db_direction {
                    Direction::Left => {
                        (sibling.as_ref().unwrap().read().unwrap().left.as_ref().map_or(Color::Black, |rc| rc.read().unwrap().color),
                            sibling.as_ref().unwrap().read().unwrap().right.as_ref().map_or(Color::Black, |rc| rc.read().unwrap().color))
                    }
                    Direction::Right => {
                        (sibling.as_ref().unwrap().read().unwrap().right.as_ref().map_or(Color::Black, |rc| rc.read().unwrap().color),
                            sibling.as_ref().unwrap().read().unwrap().left.as_ref().map_or(Color::Black, |rc| rc.read().unwrap().color))
                    }
                };

                match (sibling_far_child_color, sibling_near_child_color) {
                    (Color::Black, Color::Black) => {
                        // case 3
                        // make sibling red
                        sibling.as_ref().unwrap().write().unwrap().color = Color::Red;
                        let parent = db_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade());
                        let parent_color = parent.as_ref().unwrap().read().unwrap().color;
                        match parent_color {
                            Color::Red => {
                                // make it black
                                parent.as_ref().unwrap().write().unwrap().color = Color::Black;
                            }
                            Color::Black => {
                                // parent becomes double black; rerun this for parent
                                self.resolve_double_black(parent, None);
                            }
                        }
                    }
                    (Color::Black, Color::Red) => {
                        // case 5
                        // swap color of sibling with near child
                        let sibling_near_child = match db_direction {
                            Direction::Left => sibling.as_ref().unwrap().read().unwrap().left.clone(),
                            Direction::Right => sibling.as_ref().unwrap().read().unwrap().right.clone(),
                        };
                        // we already know near child is red and sibling is black, so no need for checking
                        sibling.as_ref().unwrap().write().unwrap().color = Color::Red;
                        sibling_near_child.as_ref().unwrap().write().unwrap().color = Color::Black;
                        // rotate at sibling in opposite direction of db_node
                        self.rotate_subtree(sibling, db_direction.opposite());
                        // rerun this for the same node (will probably be case 6)
                        self.resolve_double_black(db_node, Some(db_direction));
                    }
                    (Color::Red, _) => {
                        // case 6
                        // swap parent color with sibling color
                        let parent = db_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade());
                        let parent_color = parent.as_ref().unwrap().read().unwrap().color;
                        // we know the sibling is black so just color the parent black
                        parent.as_ref().unwrap().write().unwrap().color = Color::Black;
                        sibling.as_ref().unwrap().write().unwrap().color = parent_color;
                        // grab sibling's far child
                        let sibling_far_child = match db_direction {
                            Direction::Left => sibling.as_ref().unwrap().read().unwrap().right.clone(),
                            Direction::Right => sibling.as_ref().unwrap().read().unwrap().left.clone(),
                        };
                        // rotate at parent node towards db_node
                        self.rotate_subtree(parent, db_direction);
                        // color sibling_far_child black
                        sibling_far_child.as_ref().unwrap().write().unwrap().color = Color::Black;
                    }
                }
            },
            Color::Red => {
                // case 4
                // swap parent color with sibling color
                let parent = db_node.as_ref().unwrap().read().unwrap().parent.as_ref().and_then(|weak| weak.upgrade());
                let parent_color = parent.as_ref().unwrap().read().unwrap().color;
                // we know the sibling is red so just color the parent red
                parent.as_ref().unwrap().write().unwrap().color = Color::Red;
                sibling.as_ref().unwrap().write().unwrap().color = parent_color;
                // rotate at parent node towards db_node
                self.rotate_subtree(parent, db_direction);
                // rerun this for the same node
                self.resolve_double_black(db_node, Some(db_direction));
            }
        }
    }

    fn rebalance_at_point(&mut self, node: Link<T>) {
        // base case
        if Arc::ptr_eq(node.as_ref().unwrap(), self.root.as_ref().unwrap()) {
            // hit the root; make sure it's colored black and return
            self.root.as_ref().unwrap().write().unwrap().color = Color::Black;
            return;
        }

        // get parent
        let parent = node.as_ref().unwrap().read().unwrap().parent.as_ref().unwrap().upgrade();

        if parent.as_ref().unwrap().read().unwrap().color == Color::Black {
            // nothing to do here
            return;
        }

        // get grandparent and uncle
        let grandparent = parent.as_ref().unwrap().read().unwrap().parent.as_ref().unwrap().upgrade();
        let uncle = match Node::direction(parent.as_ref()).unwrap() {
            Direction::Left => grandparent.as_ref().unwrap().read().unwrap().right.clone(),
            Direction::Right => grandparent.as_ref().unwrap().read().unwrap().left.clone(),
        };

        match uncle.as_ref().map_or(Color::Black, |rc| rc.read().unwrap().color) {
            Color::Red => {
                // color parent and uncle black
                parent.as_ref().unwrap().write().unwrap().color = Color::Black;
                uncle.as_ref().unwrap().write().unwrap().color = Color::Black;
                // color grandparent red
                grandparent.as_ref().unwrap().write().unwrap().color = Color::Red;
                // continue balancing from grandparent
                self.rebalance_at_point(grandparent);
            }
            Color::Black => {
                let node_direction = Node::direction(node.as_ref()).unwrap();
                let parent_direction = Node::direction(parent.as_ref()).unwrap();

                match (parent_direction, node_direction) {
                    (Direction::Left, Direction::Left) => {
                        // right rotate on grandparent
                        self.rotate_subtree(grandparent.clone(), Direction::Right);
                        // swap colors of grandparent and parent
                        let parent_color = parent.as_ref().unwrap().read().unwrap().color;
                        parent.as_ref().unwrap().write().unwrap().color = grandparent.as_ref().unwrap().read().unwrap().color;
                        grandparent.as_ref().unwrap().write().unwrap().color = parent_color;
                    }
                    (Direction::Left, Direction::Right) => {
                        // left rotation on parent
                        self.rotate_subtree(parent.clone(), Direction::Left);
                        // right rotate on grandparent
                        self.rotate_subtree(grandparent.clone(), Direction::Right);
                        // swap colors of grandparent and node
                        let node_color = node.as_ref().unwrap().read().unwrap().color;
                        node.as_ref().unwrap().write().unwrap().color = grandparent.as_ref().unwrap().read().unwrap().color;
                        grandparent.as_ref().unwrap().write().unwrap().color = node_color;
                    }
                    (Direction::Right, Direction::Left) => {
                        // right rotate on parent
                        self.rotate_subtree(parent.clone(), Direction::Right);
                        // left rotate on grandparent
                        self.rotate_subtree(grandparent.clone(), Direction::Left);
                        // swap colors of grandparent and node
                        let node_color = node.as_ref().unwrap().read().unwrap().color;
                        node.as_ref().unwrap().write().unwrap().color = grandparent.as_ref().unwrap().read().unwrap().color;
                        grandparent.as_ref().unwrap().write().unwrap().color = node_color;
                    }
                    (Direction::Right, Direction::Right) => {
                        // left rotate on grandparent
                        self.rotate_subtree(grandparent.clone(), Direction::Left);
                        // swap colors of grandparent and parent
                        let parent_color = parent.as_ref().unwrap().read().unwrap().color;
                        parent.as_ref().unwrap().write().unwrap().color = grandparent.as_ref().unwrap().read().unwrap().color;
                        grandparent.as_ref().unwrap().write().unwrap().color = parent_color;
                    }
                }
            }
        }
    }

    fn rotate_subtree(&mut self, subtree_root: Link<T>, direction: Direction) {
        if subtree_root.is_none() {
            return;
        }

        let subtree_parent = subtree_root.as_ref().unwrap().read().unwrap().parent.clone();
        let subtree_direction = Node::direction(subtree_root.as_ref());
        let pivot = match direction {
            Direction::Left => {
                let pivot = subtree_root.as_ref().unwrap().read().unwrap().right.clone();
                // point subtree_root->right at pivot->left and rewire parent
                subtree_root.as_ref().unwrap().write().unwrap().right = pivot.as_ref().unwrap().read().unwrap().left.clone();
                if subtree_root.as_ref().unwrap().read().unwrap().right.is_some() {
                    subtree_root.as_ref().unwrap().read().unwrap().right.as_ref().unwrap().write().unwrap().parent = Some(Arc::downgrade(subtree_root.as_ref().unwrap()));
                }
                // point pivot->left at subtree_root
                pivot.as_ref().unwrap().write().unwrap().left = subtree_root.clone();
                pivot
            }
            Direction::Right => {
                let pivot = subtree_root.as_ref().unwrap().read().unwrap().left.clone();
                // point subtree_root->left at pivot->right and rewire parent
                subtree_root.as_ref().unwrap().write().unwrap().left = pivot.as_ref().unwrap().read().unwrap().right.clone();
                if subtree_root.as_ref().unwrap().read().unwrap().left.is_some() {
                    subtree_root.as_ref().unwrap().read().unwrap().left.as_ref().unwrap().write().unwrap().parent = Some(Arc::downgrade(subtree_root.as_ref().unwrap()));
                }
                // point pivot->right at subtree_root
                pivot.as_ref().unwrap().write().unwrap().right = subtree_root.clone();
                pivot
            }
        };

        // rewire subtree_root's parent
        subtree_root.as_ref().unwrap().write().unwrap().parent = Some(Arc::downgrade(pivot.as_ref().unwrap()));

        // rewire subtree_parent
        if let Some(subtree_direction) = subtree_direction {
            match subtree_direction {
                Direction::Left => {
                    subtree_parent.as_ref().unwrap().upgrade().unwrap().write().unwrap().left = pivot.clone();
                }
                Direction::Right => {
                    subtree_parent.as_ref().unwrap().upgrade().unwrap().write().unwrap().right = pivot.clone();
                }
            }
            pivot.as_ref().unwrap().write().unwrap().parent = subtree_parent;
        } else {
            // subtree_root was root; reassign root and make parent None
            self.root = pivot.clone();
            pivot.as_ref().unwrap().write().unwrap().parent = None;
        }
    }

    fn inorder_traversal(&self) -> Vec<Link<T>> {
        Self::inorder_traversal_recursive(self.root.clone())
    }

    fn inorder_traversal_recursive(node: Link<T>) -> Vec<Link<T>> {
        // base case
        if node.is_none() {
            return vec![];
        }

        // generate recursively
        let mut vec = vec![];

        vec.append(&mut Self::inorder_traversal_recursive(node.as_ref().unwrap().read().unwrap().left.clone()));
        vec.push(node.clone());
        vec.append(&mut Self::inorder_traversal_recursive(node.as_ref().unwrap().read().unwrap().right.clone()));
        vec
    }
}

impl<T: Clone + Ord> Default for RedBlackTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Ord> FromIterator<T> for RedBlackTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut tree = Self::new();

        for val in iter {
            tree.insert(val);
        }

        tree
    }
}

impl<T: Clone + Ord> From<RedBlackTree<T>> for Vec<T> {
    fn from(value: RedBlackTree<T>) -> Self {
        // get the inorder traversal and convert to a Vec<T>
        value.inorder_traversal().into_iter().map(|node| node.as_ref().unwrap().read().unwrap().val.clone()).collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::rbt;

    use super::RedBlackTree;

    #[test]
    fn basics() {
        // create tree and insert some values
        let mut tree = RedBlackTree::new();
        let mut check_size = 0;
        for i in 1..=30 {
            // only insert values divisible by 2, 3, or 5
            if i % 2 == 0 || i % 3 == 0 || i % 5 == 0 {
                // make sure insertion actually works
                assert_eq!(tree.insert(i), true);
                // make sure size goes up
                check_size += 1;
                assert_eq!(tree.size(), check_size);
            }
        }
        println!("{tree:?}");
        // do some checks with the values we just went over
        for i in 1..=30 {
            if i % 2 == 0 || i % 3 == 0 || i % 5 == 0 {
                // make sure values already in the tree cannot be inserted again, but can be found
                assert_eq!(tree.insert(i), false);
                // make sure these values can be found
                assert_eq!(tree.contains(i), true);
                // try removing the value
                println!("removing {i}");
                assert_eq!(tree.remove(i), true);
                // make sure size goes down
                check_size -= 1;
                assert_eq!(tree.size(), check_size);
                println!("{tree:?}");
                println!();
                // make sure that we cannot find the value after removal
                assert_eq!(tree.contains(i), false);
            } else {
                // make sure *these* values cannot be found
                assert_eq!(tree.contains(i), false);
            }
        }
    }

    #[test]
    fn test_macro() {
        // test value form
        let list_tree = rbt![1, 2, 3, 4];
        assert_eq!(list_tree.contains(1), true);
        assert_eq!(list_tree.contains(2), true);
        assert_eq!(list_tree.contains(3), true);
        assert_eq!(list_tree.contains(4), true);
        // test iterator form
        let iter_tree = rbt!(i in 1..=15);
        for i in 1..=15 {
            assert_eq!(iter_tree.contains(i), true);
        }
        // make sure iterator form works with the relatively complex iterator from the main tests
        let mut complex_iter_tree = rbt!(i in (1..=30).filter(|i| i % 2 == 0 || i % 3 == 0 || i % 5 == 0));
        let mut check_size = complex_iter_tree.size();
        for i in 1..=30 {
            if i % 2 == 0 || i % 3 == 0 || i % 5 == 0 {
                // make sure values already in the tree cannot be inserted again, but can be found
                assert_eq!(complex_iter_tree.insert(i), false);
                // make sure these values can be found
                assert_eq!(complex_iter_tree.contains(i), true);
                // try removing the value
                println!("removing {i}");
                assert_eq!(complex_iter_tree.remove(i), true);
                // make sure size goes down
                check_size -= 1;
                assert_eq!(complex_iter_tree.size(), check_size);
                println!("{complex_iter_tree:?}");
                println!();
                // make sure that we cannot find the value after removal
                assert_eq!(complex_iter_tree.contains(i), false);
            } else {
                // make sure *these* values cannot be found
                assert_eq!(complex_iter_tree.contains(i), false);
            }
        }
    }
}
