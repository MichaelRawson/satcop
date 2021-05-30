use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

pub(crate) struct Id<T> {
    index: u32,
    _phantom: PhantomData<T>,
}

impl<T> Id<T> {
    #[inline]
    pub(crate) const fn new(index: u32) -> Self {
        let _phantom = PhantomData;
        Self { index, _phantom }
    }

    #[inline]
    pub(crate) fn as_u32(self) -> u32 {
        self.index
    }

    #[inline]
    pub(crate) fn offset(self, offset: u32) -> Self {
        Self::new(self.index + offset)
    }

    #[inline]
    pub(crate) fn increment(&mut self) {
        self.index += 1;
    }
}

impl<T> Clone for Id<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(self.index)
    }
}

impl<T> Copy for Id<T> {}

impl<T> Default for Id<T> {
    fn default() -> Self {
        Id::new(0)
    }
}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{}", self.index)
    }
}

impl<T> PartialEq for Id<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for Id<T> {}

impl<T> PartialOrd for Id<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.index.partial_cmp(&other.index)
    }
}

impl<T> Ord for Id<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index.cmp(&other.index)
    }
}

impl<T> Hash for Id<T> {
    #[inline]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.index.hash(hasher);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Off<T> {
    pub(crate) id: Id<T>,
    pub(crate) offset: u32,
}

impl<T> Off<T> {
    #[inline]
    pub(crate) fn new(id: Id<T>, offset: u32) -> Self {
        Self { id, offset }
    }
}

pub(crate) struct Range<T> {
    pub(crate) start: Id<T>,
    pub(crate) stop: Id<T>,
}

impl<T> Range<T> {
    #[inline]
    pub(crate) fn new(start: Id<T>, stop: Id<T>) -> Self {
        debug_assert!(start <= stop);
        Self { start, stop }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.start == self.stop
    }
}

impl<T> Clone for Range<T> {
    #[inline]
    fn clone(&self) -> Self {
        let start = self.start;
        let stop = self.stop;
        Self { start, stop }
    }
}

impl<T> Copy for Range<T> {}

impl<T> fmt::Debug for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}-{:?}", self.start, self.stop)
    }
}

impl<T> IntoIterator for Range<T> {
    type Item = Id<T>;
    type IntoIter = RangeIterator<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let start = self.start;
        let stop = self.stop;
        let _phantom = PhantomData;
        RangeIterator {
            start,
            stop,
            _phantom,
        }
    }
}

pub(crate) struct RangeIterator<T> {
    start: Id<T>,
    stop: Id<T>,
    _phantom: PhantomData<T>,
}

impl<T> Iterator for RangeIterator<T> {
    type Item = Id<T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.stop {
            return None;
        }
        let next = self.start;
        self.start.index += 1;
        Some(next)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = (self.stop.index - self.start.index) as usize;
        (size, Some(size))
    }
}

impl<T> ExactSizeIterator for RangeIterator<T> {}

#[derive(Debug)]
pub(crate) struct Block<T>(Vec<T>);

impl<T> Block<T> {
    #[inline]
    pub(crate) fn len(&self) -> Id<T> {
        let len = self.0.len();
        Id::new(len as u32)
    }

    #[inline]
    pub(crate) fn resize_with<F>(&mut self, max: Id<T>, f: F)
    where
        F: FnMut() -> T,
    {
        let index = max.index as usize;
        self.0.resize_with(index, f);
    }

    #[inline]
    pub(crate) fn range(&self) -> Range<T> {
        Range::new(Id::default(), self.len())
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    #[inline]
    pub(crate) fn truncate(&mut self, len: Id<T>) {
        self.0.truncate(len.index as usize);
    }

    #[inline]
    pub(crate) fn push(&mut self, t: T) -> Id<T> {
        let id = self.len();
        self.0.push(t);
        id
    }

    #[inline]
    pub(crate) fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

impl<T> Default for Block<T> {
    #[inline]
    fn default() -> Self {
        Self(vec![])
    }
}

impl<T> Index<Id<T>> for Block<T> {
    type Output = T;
    #[inline]
    fn index(&self, id: Id<T>) -> &Self::Output {
        debug_assert!(id < self.len());
        let index = id.index as usize;
        unsafe { self.0.get_unchecked(index) }
    }
}

impl<T> IndexMut<Id<T>> for Block<T> {
    #[inline]
    fn index_mut(&mut self, id: Id<T>) -> &mut Self::Output {
        debug_assert!(id < self.len());
        let index = id.index as usize;
        unsafe { self.0.get_unchecked_mut(index) }
    }
}

impl<T> Index<Range<T>> for Block<T> {
    type Output = [T];
    #[inline]
    fn index(&self, range: Range<T>) -> &Self::Output {
        debug_assert!(range.start <= range.stop);
        debug_assert!(range.stop <= self.len());
        let start = range.start.index as usize;
        let stop = range.stop.index as usize;
        unsafe { self.0.get_unchecked(start..stop) }
    }
}

impl<T> IndexMut<Range<T>> for Block<T> {
    #[inline]
    fn index_mut(&mut self, range: Range<T>) -> &mut Self::Output {
        debug_assert!(range.start <= range.stop);
        debug_assert!(range.stop <= self.len());
        let start = range.start.index as usize;
        let stop = range.stop.index as usize;
        unsafe { self.0.get_unchecked_mut(start..stop) }
    }
}

#[derive(Debug)]
pub(crate) struct BlockMap<K, V> {
    block: Block<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> BlockMap<K, V> {
    #[inline]
    pub(crate) fn len(&self) -> Id<K> {
        Id::new(self.block.len().index)
    }

    #[inline]
    pub(crate) fn range(&self) -> Range<K> {
        Range::new(Id::default(), self.len())
    }

    #[inline]
    pub(crate) fn push(&mut self, v: V) -> Id<K> {
        Id::new(self.block.push(v).index)
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.block.clear();
    }

    #[inline]
    pub(crate) fn resize_with<F>(&mut self, max: Id<K>, f: F)
    where
        F: FnMut() -> V,
    {
        let len = Id::new(max.index);
        self.block.resize_with(len, f);
    }
}

impl<K, V> Index<Id<K>> for BlockMap<K, V> {
    type Output = V;
    #[inline]
    fn index(&self, id: Id<K>) -> &Self::Output {
        let id = Id::new(id.index);
        &self.block[id]
    }
}

impl<K, V> IndexMut<Id<K>> for BlockMap<K, V> {
    #[inline]
    fn index_mut(&mut self, id: Id<K>) -> &mut Self::Output {
        let id = Id::new(id.index);
        &mut self.block[id]
    }
}

impl<K, V> Default for BlockMap<K, V> {
    #[inline]
    fn default() -> Self {
        let block = Block::default();
        let _phantom = PhantomData;
        Self { block, _phantom }
    }
}
