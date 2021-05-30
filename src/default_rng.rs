use rand::rngs::SmallRng;
use rand::SeedableRng;

pub(crate) struct DefaultRng(pub(crate) SmallRng);

impl Default for DefaultRng {
    fn default() -> Self {
        Self(SmallRng::seed_from_u64(0))
    }
}
