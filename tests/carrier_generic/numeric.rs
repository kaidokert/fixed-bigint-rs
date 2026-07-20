use crate::harness::*;

// Identity (`one`) and the width bounds (`min`/`max`). At the pinned 32-bit
// width, min is zero and max is the 32-bit max on every backing.
#[test]
fn one_and_bounds() {
    fn body<C: Carrier>() {
        assert_eq!(C::one(), C::from_u32(1));
        assert!(One::is_one(&C::from_u32(1)));
        assert!(!One::is_one(&C::from_u32(0)));

        assert_eq!(C::min_value(), C::from_u32(0));
        assert_eq!(C::max_value(), C::from_u32(MAX32));
    }
    for_both_carriers!(body);
}

// `num_integer::Roots` and `num_integer::Integer` are compiled only under the
// `num-traits` feature (which pulls in `num-integer`), so their shared coverage
// is gated to match — unlike the always-available const-num-traits surface.
#[cfg(feature = "num-traits")]
#[test]
fn roots_and_integer() {
    fn body<C: Carrier + num_integer::Roots + num_integer::Integer>() {
        use num_integer::{Integer, Roots};

        // Roots truncate toward zero, including at the width extremes.
        assert_eq!(Roots::sqrt(&C::from_u32(0)), C::from_u32(0));
        assert_eq!(Roots::sqrt(&C::from_u32(144)), C::from_u32(12));
        assert_eq!(Roots::sqrt(&C::from_u32(145)), C::from_u32(12));
        // floor(sqrt(2^32 - 1)) = 0xFFFF.
        assert_eq!(Roots::sqrt(&C::max_value()), C::from_u32(0xFFFF));
        assert_eq!(Roots::cbrt(&C::from_u32(0)), C::from_u32(0));
        assert_eq!(Roots::cbrt(&C::from_u32(27)), C::from_u32(3));
        // floor(cbrt(2^32 - 1)) = 1625 (1625^3 <= max < 1626^3).
        assert_eq!(Roots::cbrt(&C::max_value()), C::from_u32(1625));
        assert_eq!(Roots::nth_root(&C::from_u32(81), 4), C::from_u32(3));

        // Integer: gcd / lcm / floored div-mod / div_rem / parity, with the
        // zero-operand identities pinned (gcd(x,0)=x, lcm anything-0 = 0).
        assert_eq!(
            Integer::gcd(&C::from_u32(0), &C::from_u32(0)),
            C::from_u32(0)
        );
        assert_eq!(
            Integer::gcd(&C::from_u32(10), &C::from_u32(0)),
            C::from_u32(10)
        );
        assert_eq!(
            Integer::gcd(&C::max_value(), &C::from_u32(0)),
            C::max_value()
        );
        assert_eq!(
            Integer::gcd(&C::from_u32(48), &C::from_u32(36)),
            C::from_u32(12)
        );
        assert_eq!(
            Integer::lcm(&C::from_u32(0), &C::from_u32(0)),
            C::from_u32(0)
        );
        assert_eq!(
            Integer::lcm(&C::from_u32(10), &C::from_u32(0)),
            C::from_u32(0)
        );
        assert_eq!(
            Integer::lcm(&C::from_u32(4), &C::from_u32(6)),
            C::from_u32(12)
        );
        assert_eq!(
            Integer::div_floor(&C::from_u32(17), &C::from_u32(5)),
            C::from_u32(3)
        );
        assert_eq!(
            Integer::mod_floor(&C::from_u32(17), &C::from_u32(5)),
            C::from_u32(2)
        );
        assert_eq!(
            Integer::div_rem(&C::from_u32(17), &C::from_u32(5)),
            (C::from_u32(3), C::from_u32(2))
        );
        assert!(Integer::is_even(&C::from_u32(10)));
        assert!(Integer::is_odd(&C::from_u32(7)));
    }
    for_both_carriers!(body);
}

#[test]
fn euclid_absdiff_midpoint() {
    fn body<C: Carrier>() {
        // Euclid: unsigned, so == ordinary div/rem.
        assert_eq!(
            Euclid::div_euclid(C::from_u32(17), C::from_u32(5)),
            C::from_u32(3)
        );
        assert_eq!(
            Euclid::rem_euclid(C::from_u32(17), C::from_u32(5)),
            C::from_u32(2)
        );
        assert_eq!(
            Euclid::div_rem_euclid(C::from_u32(17), C::from_u32(5)),
            (C::from_u32(3), C::from_u32(2))
        );
        assert_eq!(
            CheckedEuclid::checked_rem_euclid(C::from_u32(17), C::from_u32(5)),
            Some(C::from_u32(2))
        );
        assert_eq!(
            CheckedEuclid::checked_div_euclid(C::from_u32(17), C::from_u32(0)),
            None
        );
        assert_eq!(
            CheckedEuclid::checked_rem_euclid(C::from_u32(17), C::from_u32(0)),
            None
        );
        // checked_div_rem_euclid carries its own zero guard — pin both paths.
        assert_eq!(
            CheckedEuclid::checked_div_rem_euclid(C::from_u32(17), C::from_u32(5)),
            Some((C::from_u32(3), C::from_u32(2)))
        );
        assert_eq!(
            CheckedEuclid::checked_div_rem_euclid(C::from_u32(17), C::from_u32(0)),
            None
        );

        // abs_diff, both orders.
        assert_eq!(
            AbsDiff::abs_diff(C::from_u32(10), C::from_u32(3)),
            C::from_u32(7)
        );
        assert_eq!(
            AbsDiff::abs_diff(C::from_u32(3), C::from_u32(10)),
            C::from_u32(7)
        );

        // midpoint averages without overflow.
        assert_eq!(
            Midpoint::midpoint(C::from_u32(10), C::from_u32(20)),
            C::from_u32(15)
        );
        let max = C::from_u32(MAX32);
        assert_eq!(Midpoint::midpoint(max, max), max); // (max + max) / 2 = max
    }
    for_both_carriers!(body);
}

#[test]
fn power_of_two_and_multiples() {
    fn body<C: Carrier>() {
        // is_power_of_two.
        assert!(!IsPowerOfTwo::is_power_of_two(C::from_u32(0)));
        for p in [1u32, 2, 4, 8, 128, 256, 0x8000_0000] {
            assert!(IsPowerOfTwo::is_power_of_two(C::from_u32(p)));
        }
        for np in [3u32, 5, 6, 7, 100, 255] {
            assert!(!IsPowerOfTwo::is_power_of_two(C::from_u32(np)));
        }

        // next_power_of_two.
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(C::from_u32(0)),
            C::from_u32(1)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(C::from_u32(5)),
            C::from_u32(8)
        );
        assert_eq!(
            NextPowerOfTwo::next_power_of_two(C::from_u32(128)),
            C::from_u32(128)
        );
        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(C::from_u32(100)),
            Some(C::from_u32(128))
        );
        // 2^31 + 1 rounds up to 2^32, which overflows the 32-bit width.
        assert_eq!(
            NextPowerOfTwo::checked_next_power_of_two(C::from_u32(0x8000_0001)),
            None
        );
        assert_eq!(
            NextPowerOfTwo::wrapping_next_power_of_two(C::from_u32(0x8000_0001)),
            C::from_u32(0)
        );

        // MultipleOf: zero divisor is false (const-num-traits convention).
        assert!(MultipleOf::is_multiple_of(C::from_u32(10), C::from_u32(5)));
        assert!(!MultipleOf::is_multiple_of(C::from_u32(11), C::from_u32(5)));
        assert!(!MultipleOf::is_multiple_of(C::from_u32(10), C::from_u32(0)));

        // NextMultipleOf.
        assert_eq!(
            NextMultipleOf::next_multiple_of(C::from_u32(11), C::from_u32(5)),
            C::from_u32(15)
        );
        assert_eq!(
            NextMultipleOf::next_multiple_of(C::from_u32(10), C::from_u32(5)),
            C::from_u32(10)
        );
        // rhs greater than self: the next multiple is rhs itself.
        assert_eq!(
            NextMultipleOf::next_multiple_of(C::from_u32(3), C::from_u32(10)),
            C::from_u32(10)
        );
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(C::from_u32(10), C::from_u32(0)),
            None
        );
        // self + (rhs - rem) overflows the 32-bit width.
        assert_eq!(
            NextMultipleOf::checked_next_multiple_of(C::from_u32(MAX32), C::from_u32(10)),
            None
        );
    }
    for_both_carriers!(body);
}

#[test]
fn isqrt_and_ilogs() {
    fn body<C: Carrier>() {
        // isqrt: floor square root.
        assert_eq!(Isqrt::isqrt(C::from_u32(0)), C::from_u32(0));
        assert_eq!(Isqrt::isqrt(C::from_u32(15)), C::from_u32(3));
        assert_eq!(Isqrt::isqrt(C::from_u32(16)), C::from_u32(4));
        assert_eq!(Isqrt::isqrt(C::from_u32(1_000_000)), C::from_u32(1000));
        assert_eq!(Isqrt::isqrt(C::from_u32(MAX32)), C::from_u32(0xFFFF));

        // ilog2 / ilog10 / ilog.
        assert_eq!(Ilog2::ilog2(C::from_u32(8)), 3);
        assert_eq!(Ilog2::ilog2(C::from_u32(0x8000_0000)), 31);
        assert_eq!(Ilog2::checked_ilog2(C::from_u32(0)), None);
        assert_eq!(Ilog10::ilog10(C::from_u32(9999)), 3);
        assert_eq!(Ilog10::ilog10(C::from_u32(1_000_000_000)), 9);
        assert_eq!(Ilog10::checked_ilog10(C::from_u32(0)), None);
        assert_eq!(Ilog::ilog(C::from_u32(27), C::from_u32(3)), 3);
        assert_eq!(Ilog::checked_ilog(C::from_u32(10), C::from_u32(1)), None);
    }
    for_both_carriers!(body);
}
