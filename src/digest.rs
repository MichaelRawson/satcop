use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hash, Hasher};

const FNV1A_PRIME: u128 = 0x0000000001000000000000000000013B;
const FNV1A_OFFSET_BASIS: u128 = 0x6c62272e07bb014262b821756295c58d;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Digest(pub(crate) u128);

impl Default for Digest {
    #[inline]
    fn default() -> Self {
        Self(FNV1A_OFFSET_BASIS)
    }
}

impl Digest {
    #[inline]
    pub(crate) fn update<T: Into<u128>>(&mut self, value: T) {
        self.0 = (self.0 ^ value.into()).wrapping_mul(FNV1A_PRIME);
    }
}

pub(crate) struct DigestHasher(u64);

impl Hasher for DigestHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _data: &[u8]) {
        unreachable!("should only be used with 128-bit digest")
    }

    #[inline]
    fn write_u128(&mut self, data: u128) {
        self.0 = data as u64;
    }
}

#[derive(Default)]
pub(crate) struct DigestHasherBuilder;

impl BuildHasher for DigestHasherBuilder {
    type Hasher = DigestHasher;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        DigestHasher(0)
    }
}

pub(crate) type DigestSet = HashSet<Digest, DigestHasherBuilder>;
pub(crate) type DigestMap<T> = HashMap<Digest, T, DigestHasherBuilder>;