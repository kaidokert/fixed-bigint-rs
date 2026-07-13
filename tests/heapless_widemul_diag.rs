//! Diagnostic: HeaplessBigInt<T,CAP>.wide_mul must match FixedUInt<T,CAP>
//! for ALL operand lens — WideMul splits at the carrier's fixed width,
//! and wide-REDC reconstructs `hi·2^(carrier_width) + lo` against that.
//! ed25519's field-param setup does wide_mul(small, small) (e.g.
//! r2_mod_n = 38*38), where a max(operand-len) split diverges.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{CarryingMul, Nct, Zero};
use fixed_bigint::{FixedUInt, HeaplessBigInt};
use num_traits::ToPrimitive;

type H = HeaplessBigInt<u32, 8, Nct>;
type F = FixedUInt<u32, 8, Nct>;

// (lo, hi) of both carriers must agree limb-for-limb over the full CAP.
fn assert_wide_mul_matches(a: u32, b: u32, alen: u16, blen: u16) {
    let ha = H::from_limbs(
        {
            let mut l = [0u32; 8];
            l[0] = a;
            l
        },
        alen,
    );
    let hb = H::from_limbs(
        {
            let mut l = [0u32; 8];
            l[0] = b;
            l
        },
        blen,
    );
    let (hlo, hhi) = ha.carrying_mul(hb, <H as Zero>::zero());

    let fa = F::from(a);
    let fb = F::from(b);
    let (flo, fhi) = fa.carrying_mul(fb, <F as Zero>::zero());

    // Compare each half limb-for-limb across the whole container.
    for i in 0..8 {
        assert_eq!(
            hlo.all_limbs()[i],
            flo.words()[i],
            "lo limb {i}: wide_mul({a}@{alen} * {b}@{blen})"
        );
        assert_eq!(
            hhi.all_limbs()[i],
            fhi.words()[i],
            "hi limb {i}: wide_mul({a}@{alen} * {b}@{blen})"
        );
    }
    let _ = (flo.to_u64(), fhi.to_u64());
}

#[test]
fn wide_mul_matches_fixeduint_for_small_operands() {
    // The ed25519 r2_mod_n shape: 38 * 38 = 1444, both operands len 1.
    assert_wide_mul_matches(38, 38, 1, 1);
    // And a range of sub-width / mixed-width pairs.
    for &(a, b) in &[(7u32, 7u32), (1444, 1), (0xFFFF_FFFF, 2), (100, 200)] {
        assert_wide_mul_matches(a, b, 1, 1);
        assert_wide_mul_matches(a, b, 8, 1);
        assert_wide_mul_matches(a, b, 1, 8);
        assert_wide_mul_matches(a, b, 8, 8);
    }
}
