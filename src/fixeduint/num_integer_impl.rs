use super::{FixedUInt, MachineWord};

use num_traits::{PrimInt, Zero};

// Most code here from num_integer crate, unsigned implementation

impl<T: MachineWord, const N: usize> num_integer::Integer for FixedUInt<T, N> {
    fn div_floor(&self, other: &Self) -> Self {
        *self / *other
    }
    fn mod_floor(&self, other: &Self) -> Self {
        *self % *other
    }
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        let zero = Self::zero();
        if m == zero || n == zero {
            return m | n;
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros();

        // divide n and m by 2 until odd
        m = m >> m.trailing_zeros();
        n = n >> n.trailing_zeros();

        while m != n {
            if m > n {
                m -= n;
                m = m >> m.trailing_zeros();
            } else {
                n -= m;
                n = n >> n.trailing_zeros();
            }
        }
        m << shift
    }
    fn lcm(&self, other: &Self) -> Self {
        if self.is_zero() && other.is_zero() {
            return Self::zero();
        }
        let gcd = self.gcd(other);
        *self * (*other / gcd)
    }
    fn divides(&self, other: &Self) -> bool {
        self.is_multiple_of(other)
    }
    fn is_multiple_of(&self, other: &Self) -> bool {
        (*self) % other == Self::zero()
    }
    fn is_even(&self) -> bool {
        // O(1): only check LSB of first word, not full-width AND + compare
        self.array[0] & T::one() == T::zero()
    }
    fn is_odd(&self) -> bool {
        self.array[0] & T::one() != T::zero()
    }
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        self.div_rem(other)
    }
}
