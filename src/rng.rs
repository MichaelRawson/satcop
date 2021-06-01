use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

pub(crate) struct DefaultRng(SmallRng);

impl DefaultRng {
    #[inline]
    pub(crate) fn get(&mut self) -> &mut impl Rng {
        &mut self.0
    }
}

impl Default for DefaultRng {
    fn default() -> Self {
        Self(SmallRng::seed_from_u64(0))
    }
}
