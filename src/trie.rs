use fnv::FnvHashMap;
use std::hash::Hash;

pub(crate) struct Trie<K, V> {
    pub(crate) value: Option<V>,
    children: FnvHashMap<K, Trie<K, V>>,
}

impl<K: Eq + Hash, V> Trie<K, V> {
    pub(crate) fn next(&mut self, key: K) -> &mut Self {
        self.children.entry(key).or_default()
        /*
        let index = self
            .children
            .binary_search_by_key(&&key, |(edge, _)| edge)
            .unwrap_or_else(|index| {
                self.children.insert(index, (key, Trie::default()));
                index
            });
        &mut self.children[index].1
        */
    }
}

impl<K, V> Default for Trie<K, V> {
    fn default() -> Self {
        let value = None;
        let children = FnvHashMap::default();
        Self { value, children }
    }
}
