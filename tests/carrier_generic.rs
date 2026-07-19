//! Behavior shared by every carrier — written once as a generic body and run
//! for both `FixedUInt` and `HeaplessBigInt`.
//!
//! Both carriers are pinned to the same 32-bit width so the overflow / carry /
//! wrap boundaries line up. Construction goes through the two traits both
//! carriers share — `From<u32>` then `WithPrecision::widen_to_precision(32)` —
//! because `From` alone is minimal-width on HeaplessBigInt and would otherwise
//! not match FixedUInt's fixed width.
//!
//! Tests that reach into a carrier's internals (limbs / len / CAP, personality,
//! the runtime-length width vocabulary) live in each carrier's own suite; this
//! file is only the surface both share.

use const_num_traits::{
    CarryingMul, CheckedAdd, CheckedDiv, CheckedMul, CheckedPow, CheckedRem, CheckedSub, Nct,
    OverflowingAdd, OverflowingMul, OverflowingSub, Parity, PrimBits, SaturatingAdd, SaturatingMul,
    SaturatingSub, StrictPow, WithPrecision, WrappingAdd, WrappingMul, WrappingSub, Zero,
};
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};

/// The 32-bit unsigned surface both carriers implement.
trait Carrier:
    Copy
    + core::fmt::Debug
    + PartialEq
    + PartialOrd
    + Zero
    + Parity
    + From<u32>
    + WithPrecision
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Shl<usize, Output = Self>
    + Shr<usize, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + ShlAssign<usize>
    + ShrAssign<usize>
    + WrappingAdd<Output = Self>
    + WrappingSub<Output = Self>
    + WrappingMul<Output = Self>
    + OverflowingAdd<Output = Self>
    + OverflowingSub<Output = Self>
    + OverflowingMul<Output = Self>
    + CheckedAdd<Output = Self>
    + CheckedSub<Output = Self>
    + CheckedMul<Output = Self>
    + CheckedDiv<Output = Self>
    + CheckedRem<Output = Self>
    + SaturatingAdd<Output = Self>
    + SaturatingSub<Output = Self>
    + SaturatingMul<Output = Self>
    + CarryingMul<Unsigned = Self, Output = Self>
    + Not<Output = Self>
    + PrimBits
    + CheckedPow<Output = Self>
    + StrictPow<Output = Self>
{
    /// Build `v` pinned to the carrier's full 32-bit width. `From<u32>`
    /// alone is minimal-width on HeaplessBigInt (100 → one limb), so
    /// `widen_to_precision` pins it to 32 bits — an identity on FixedUInt,
    /// a grow on HeaplessBigInt — so the overflow boundaries line up.
    fn from_u32(v: u32) -> Self {
        <Self as From<u32>>::from(v).widen_to_precision(32)
    }
}

impl<
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug + Parity,
    const N: usize,
> Carrier for FixedUInt<T, N, Nct>
{
}
impl<
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug + Parity,
    const CAP: usize,
> Carrier for HeaplessBigInt<T, CAP, Nct>
{
}

/// Run a generic body for both carriers across three backings of the same
/// 32-bit width.
macro_rules! for_both_carriers {
    ($body:ident) => {{
        $body::<FixedUInt<u8, 4, Nct>>();
        $body::<HeaplessBigInt<u8, 4, Nct>>();
        $body::<FixedUInt<u16, 2, Nct>>();
        $body::<HeaplessBigInt<u16, 2, Nct>>();
        $body::<FixedUInt<u32, 1, Nct>>();
        $body::<HeaplessBigInt<u32, 1, Nct>>();
    }};
}

const MAX32: u32 = u32::MAX;

#[test]
fn add() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(50);
        assert_eq!(a + b, C::from_u32(150));
        assert_eq!(WrappingAdd::wrapping_add(a, b), C::from_u32(150));
        assert_eq!(
            OverflowingAdd::overflowing_add(a, b),
            (C::from_u32(150), false)
        );
        assert_eq!(CheckedAdd::checked_add(a, b), Some(C::from_u32(150)));
        let mut m = a;
        m += b;
        assert_eq!(m, C::from_u32(150));

        // Overflow at the shared 32-bit width.
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        assert_eq!(WrappingAdd::wrapping_add(max, one), C::from_u32(0));
        assert_eq!(
            OverflowingAdd::overflowing_add(max, one),
            (C::from_u32(0), true)
        );
        assert_eq!(CheckedAdd::checked_add(max, one), None);
    }
    for_both_carriers!(body);
}

#[test]
fn sub() {
    fn body<C: Carrier>() {
        let a = C::from_u32(500);
        let b = C::from_u32(200);
        assert_eq!(a - b, C::from_u32(300));
        assert_eq!(WrappingSub::wrapping_sub(a, b), C::from_u32(300));
        assert_eq!(
            OverflowingSub::overflowing_sub(a, b),
            (C::from_u32(300), false)
        );
        assert_eq!(CheckedSub::checked_sub(a, b), Some(C::from_u32(300)));
        let mut m = a;
        m -= b;
        assert_eq!(m, C::from_u32(300));

        // Underflow wraps at 32 bits and reports a borrow.
        let one = C::from_u32(1);
        let two = C::from_u32(2);
        assert_eq!(WrappingSub::wrapping_sub(one, two), C::from_u32(MAX32));
        assert_eq!(
            OverflowingSub::overflowing_sub(one, two),
            (C::from_u32(MAX32), true)
        );
        assert_eq!(CheckedSub::checked_sub(one, two), None);
    }
    for_both_carriers!(body);
}

#[test]
fn mul() {
    fn body<C: Carrier>() {
        let a = C::from_u32(13);
        let b = C::from_u32(17);
        assert_eq!(a * b, C::from_u32(221));
        assert_eq!(WrappingMul::wrapping_mul(a, b), C::from_u32(221));
        assert_eq!(
            OverflowingMul::overflowing_mul(a, b),
            (C::from_u32(221), false)
        );
        assert_eq!(CheckedMul::checked_mul(a, b), Some(C::from_u32(221)));
        let mut m = a;
        m *= b;
        assert_eq!(m, C::from_u32(221));

        // 0x10000 * 0x10000 = 2^32 overflows 32 bits.
        let x = C::from_u32(0x1_0000);
        assert_eq!(WrappingMul::wrapping_mul(x, x), C::from_u32(0));
        assert_eq!(
            OverflowingMul::overflowing_mul(x, x),
            (C::from_u32(0), true)
        );
        assert_eq!(CheckedMul::checked_mul(x, x), None);
    }
    for_both_carriers!(body);
}

#[test]
fn carrying_mul_high_half() {
    fn body<C: Carrier>() {
        // 0x10000 * 0x10000 = 2^32: low half 0, high half 1.
        let x = C::from_u32(0x1_0000);
        let (lo, hi) = CarryingMul::carrying_mul(x, x, C::from_u32(0));
        assert_eq!(lo, C::from_u32(0));
        assert_eq!(hi, C::from_u32(1));
        // No overflow: 5 * 7 + 3 = 38, high half 0.
        let (lo, hi) = CarryingMul::carrying_mul(C::from_u32(5), C::from_u32(7), C::from_u32(3));
        assert_eq!(lo, C::from_u32(38));
        assert_eq!(hi, C::from_u32(0));
    }
    for_both_carriers!(body);
}

#[test]
fn bitwise() {
    fn body<C: Carrier>() {
        let a = C::from_u32(0xF0F0_F0F0);
        let b = C::from_u32(0x00FF_00FF);
        assert_eq!(a & b, C::from_u32(0x00F0_00F0));
        assert_eq!(a | b, C::from_u32(0xF0FF_F0FF));
        assert_eq!(a ^ b, C::from_u32(0xF00F_F00F));
        assert!(Zero::is_zero(&(a ^ a)));

        let mut x = a;
        x &= b;
        assert_eq!(x, C::from_u32(0x00F0_00F0));
        let mut y = a;
        y |= b;
        assert_eq!(y, C::from_u32(0xF0FF_F0FF));
        let mut z = a;
        z ^= b;
        assert_eq!(z, C::from_u32(0xF00F_F00F));
    }
    for_both_carriers!(body);
}

#[test]
fn shifts() {
    fn body<C: Carrier>() {
        let v = C::from_u32(0x0000_00AB);
        assert_eq!(v << 8, C::from_u32(0x0000_AB00));
        assert_eq!(v << 0, v);
        // Around the 32-bit width boundary: the top bit stays, shifting by
        // exactly the width (or more) truncates to zero. `shift == word_bits`
        // is the classic edge (a native `<<` there would be UB).
        assert_eq!(C::from_u32(1) << 31, C::from_u32(0x8000_0000));
        assert_eq!(C::from_u32(0x8000_0000) << 1, C::from_u32(0));
        assert_eq!(C::from_u32(1) << 32, C::from_u32(0));
        assert_eq!(C::from_u32(1) << 33, C::from_u32(0));

        let w = C::from_u32(0x0000_AB00);
        assert_eq!(w >> 8, C::from_u32(0x0000_00AB));
        assert_eq!(C::from_u32(0xDEAD_BEEF) >> 32, C::from_u32(0));
        assert_eq!(C::from_u32(0xDEAD_BEEF) >> 64, C::from_u32(0));

        let mut s = C::from_u32(0x0000_00AB);
        s <<= 8;
        assert_eq!(s, C::from_u32(0x0000_AB00));
        s >>= 8;
        assert_eq!(s, C::from_u32(0x0000_00AB));
    }
    for_both_carriers!(body);
}

#[test]
fn compare() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(200);
        assert!(a < b);
        assert!(b > a);
        assert_eq!(a, C::from_u32(100));
        assert_ne!(a, b);
        assert_eq!(a.partial_cmp(&b), Some(core::cmp::Ordering::Less));
        assert_eq!(b.partial_cmp(&a), Some(core::cmp::Ordering::Greater));
        assert_eq!(a.partial_cmp(&a), Some(core::cmp::Ordering::Equal));
    }
    for_both_carriers!(body);
}

#[test]
fn parity() {
    fn body<C: Carrier>() {
        // Both directions, so an unconditional is_even/is_odd can't slip by.
        assert!(C::from_u32(0).is_even());
        assert!(!C::from_u32(0).is_odd());
        assert!(C::from_u32(4).is_even());
        assert!(!C::from_u32(4).is_odd());
        assert!(C::from_u32(5).is_odd());
        assert!(!C::from_u32(5).is_even());
        assert!(C::from_u32(0xFFFF_FFFF).is_odd());
        assert!(!C::from_u32(0xFFFF_FFFF).is_even());
    }
    for_both_carriers!(body);
}

#[test]
fn div_rem() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(7);
        assert_eq!(a / b, C::from_u32(14));
        assert_eq!(a % b, C::from_u32(2));
        // Round-trip: (a / b) * b + a % b == a.
        assert_eq!((a / b) * b + a % b, a);
        // Dividend < divisor.
        assert_eq!(C::from_u32(3) / C::from_u32(10), C::from_u32(0));
        assert_eq!(C::from_u32(3) % C::from_u32(10), C::from_u32(3));
        // Boundary identities at the max width.
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        assert_eq!(max / one, max);
        assert_eq!(max % one, C::from_u32(0));
        assert_eq!(max / max, one);
        assert_eq!(max % max, C::from_u32(0));

        let mut q = a;
        q /= b;
        assert_eq!(q, C::from_u32(14));
        let mut r = a;
        r %= b;
        assert_eq!(r, C::from_u32(2));
    }
    for_both_carriers!(body);
}

#[test]
fn prim_bits_bit_vocabulary() {
    // Both carriers, pinned to 32-bit width, must return identical results
    // for the whole PrimBits surface plus `Not`. Absolute expectations, so
    // FixedUInt and HeaplessBigInt are checked against the same truth.
    fn body<C: Carrier>() {
        // population counts
        assert_eq!(PrimBits::count_ones(C::from_u32(0b1011)), 3);
        assert_eq!(PrimBits::count_zeros(C::from_u32(0b1011)), 29);
        // leading / trailing scans over the 32-bit width
        assert_eq!(PrimBits::leading_zeros(C::from_u32(0)), 32);
        assert_eq!(PrimBits::leading_zeros(C::from_u32(1)), 31);
        assert_eq!(PrimBits::trailing_zeros(C::from_u32(0b1000)), 3);
        assert_eq!(PrimBits::trailing_zeros(C::from_u32(0)), 32);
        assert_eq!(PrimBits::leading_ones(C::from_u32(MAX32)), 32);
        assert_eq!(PrimBits::trailing_ones(C::from_u32(0b0111)), 3);
        // rotates wrap within the 32-bit width
        assert_eq!(PrimBits::rotate_left(C::from_u32(1), 4), C::from_u32(16));
        assert_eq!(PrimBits::rotate_right(C::from_u32(16), 4), C::from_u32(1));
        assert_eq!(
            PrimBits::rotate_left(C::from_u32(0x8000_0000), 1),
            C::from_u32(1)
        );
        assert_eq!(
            PrimBits::rotate_right(C::from_u32(1), 1),
            C::from_u32(0x8000_0000)
        );
        // shifts (unsigned == signed on an unsigned carrier)
        assert_eq!(PrimBits::unsigned_shl(C::from_u32(1), 4), C::from_u32(16));
        assert_eq!(PrimBits::unsigned_shr(C::from_u32(0x10), 4), C::from_u32(1));
        assert_eq!(PrimBits::signed_shl(C::from_u32(1), 4), C::from_u32(16));
        assert_eq!(PrimBits::signed_shr(C::from_u32(0x10), 4), C::from_u32(1));
        // byte / bit order
        assert_eq!(
            PrimBits::swap_bytes(C::from_u32(0x1234_5678)),
            C::from_u32(0x7856_3412)
        );
        assert_eq!(
            PrimBits::reverse_bits(C::from_u32(1)),
            C::from_u32(0x8000_0000)
        );
        assert_eq!(
            PrimBits::to_be(C::from_u32(0x0000_00FF)),
            C::from_u32(0xFF00_0000)
        );
        assert_eq!(
            PrimBits::from_be(C::from_u32(0xFF00_0000)),
            C::from_u32(0x0000_00FF)
        );
        assert_eq!(PrimBits::to_le(C::from_u32(0x1234)), C::from_u32(0x1234));
        // complement over the width
        assert_eq!(!C::from_u32(0), C::from_u32(MAX32));
        assert_eq!(!C::from_u32(0x0F0F_0F0F), C::from_u32(0xF0F0_F0F0));
    }
    for_both_carriers!(body);
}

#[test]
fn saturating() {
    fn body<C: Carrier>() {
        let max = C::from_u32(MAX32);
        let one = C::from_u32(1);
        // add saturates up to the width max
        assert_eq!(SaturatingAdd::saturating_add(max, one), max);
        assert_eq!(
            SaturatingAdd::saturating_add(C::from_u32(100), C::from_u32(50)),
            C::from_u32(150)
        );
        // sub clamps to zero
        assert_eq!(
            SaturatingSub::saturating_sub(one, C::from_u32(2)),
            C::from_u32(0)
        );
        assert_eq!(
            SaturatingSub::saturating_sub(C::from_u32(500), C::from_u32(200)),
            C::from_u32(300)
        );
        // 2^16 * 2^16 = 2^32 overflows the width → saturates up
        let x = C::from_u32(0x1_0000);
        assert_eq!(SaturatingMul::saturating_mul(x, x), max);
        assert_eq!(
            SaturatingMul::saturating_mul(C::from_u32(13), C::from_u32(17)),
            C::from_u32(221)
        );
    }
    for_both_carriers!(body);
}

#[test]
fn checked_div_rem() {
    fn body<C: Carrier>() {
        let a = C::from_u32(100);
        let b = C::from_u32(7);
        assert_eq!(CheckedDiv::checked_div(a, b), Some(C::from_u32(14)));
        assert_eq!(CheckedRem::checked_rem(a, b), Some(C::from_u32(2)));
        // divide by zero → None (not a panic)
        let zero = C::from_u32(0);
        assert_eq!(CheckedDiv::checked_div(a, zero), None);
        assert_eq!(CheckedRem::checked_rem(a, zero), None);
    }
    for_both_carriers!(body);
}

// Display is tested in the num-traits harness (carrier_num_traits.rs): FixedUInt
// only implements Display when `num-traits` is on, so a Display bound here would
// break the feature-free build. HeaplessBigInt's own feature-independent Display
// is covered in tests/heapless_string.rs.

#[test]
fn pow() {
    fn body<C: Carrier>() {
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(2), 10),
            Some(C::from_u32(1024))
        );
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(3), 0),
            Some(C::from_u32(1))
        ); // x^0 = 1
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(5), 1),
            Some(C::from_u32(5))
        );
        assert_eq!(
            CheckedPow::checked_pow(C::from_u32(7), 3),
            Some(C::from_u32(343))
        );
        // 2^32 overflows the 32-bit width → None.
        assert_eq!(CheckedPow::checked_pow(C::from_u32(2), 32), None);
        // strict_pow returns the value when it fits.
        assert_eq!(StrictPow::strict_pow(C::from_u32(2), 10), C::from_u32(1024));
    }
    for_both_carriers!(body);
}
