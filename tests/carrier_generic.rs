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
    CarryingMul, CheckedAdd, CheckedMul, CheckedSub, Nct, OverflowingAdd, OverflowingMul,
    OverflowingSub, Parity, WithPrecision, WrappingAdd, WrappingMul, WrappingSub, Zero,
};
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
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
    + CarryingMul<Unsigned = Self, Output = Self>
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
        // Shifting past the 32-bit width truncates to zero.
        assert_eq!(C::from_u32(0x8000_0000) << 1, C::from_u32(0));

        let w = C::from_u32(0x0000_AB00);
        assert_eq!(w >> 8, C::from_u32(0x0000_00AB));
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

        let mut q = a;
        q /= b;
        assert_eq!(q, C::from_u32(14));
        let mut r = a;
        r %= b;
        assert_eq!(r, C::from_u32(2));
    }
    for_both_carriers!(body);
}
