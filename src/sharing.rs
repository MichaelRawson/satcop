use fnv::FnvHashMap;
use std::hash::Hash;

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub(crate) struct Node(u32);

pub(crate) struct Sharing<K, V> {
    fresh: Node,
    branches: FnvHashMap<(Node, K), Node>,
    leaves: FnvHashMap<Node, V>,
}

impl<K: Eq + Hash, V: Copy> Sharing<K, V> {
    pub(crate) fn start(&self) -> Node {
        Node::default()
    }

    pub(crate) fn next(&mut self, branch: Node, next: K) -> Node {
        let fresh = &mut self.fresh;
        *self.branches.entry((branch, next)).or_insert_with(|| {
            fresh.0 += 1;
            *fresh
        })
    }

    pub(crate) fn finish(&mut self, leaf: Node, new: V) -> V {
        *self.leaves.entry(leaf).or_insert(new)
    }
}

impl<K, V> Default for Sharing<K, V> {
    fn default() -> Self {
        let fresh = Node::default();
        let branches = FnvHashMap::default();
        let leaves = FnvHashMap::default();
        Self {
            fresh,
            branches,
            leaves,
        }
    }
}
