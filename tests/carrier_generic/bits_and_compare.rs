use crate::harness::*;

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
fn iter_and_bit_scan() {
    fn body<C: Carrier>() {
        // Sum / Product.
        let vals = [
            C::from_u32(1),
            C::from_u32(2),
            C::from_u32(3),
            C::from_u32(4),
        ];
        assert_eq!(vals.iter().copied().sum::<C>(), C::from_u32(10));
        assert_eq!(vals.iter().copied().product::<C>(), C::from_u32(24));

        // HighestOne / LowestOne indices.
        assert_eq!(HighestOne::highest_one(C::from_u32(0)), None);
        assert_eq!(HighestOne::highest_one(C::from_u32(0x8000_0000)), Some(31));
        assert_eq!(LowestOne::lowest_one(C::from_u32(0)), None);
        assert_eq!(LowestOne::lowest_one(C::from_u32(0xB0)), Some(4));

        // Isolate masks.
        assert_eq!(
            IsolateHighestOne::isolate_highest_one(C::from_u32(0xB4)),
            C::from_u32(0x80)
        );
        assert_eq!(
            IsolateLowestOne::isolate_lowest_one(C::from_u32(0xB4)),
            C::from_u32(0x04)
        );
        assert_eq!(
            IsolateHighestOne::isolate_highest_one(C::from_u32(0)),
            C::from_u32(0)
        );
    }
    for_both_carriers!(body);
}

#[test]
fn deposit_extract_bits() {
    fn body<C: Carrier>() {
        let mask = C::from_u32(0x5555_5555);
        let src = C::from_u32(0b1011);
        let dep = DepositBits::deposit_bits(src, mask);
        assert_eq!(dep, C::from_u32(0b0100_0101));
        // extract is the inverse over the same mask.
        assert_eq!(ExtractBits::extract_bits(dep, mask), src);
        // full mask is the identity both ways.
        let full = C::from_u32(MAX32);
        let v = C::from_u32(0x1234_5678);
        assert_eq!(DepositBits::deposit_bits(v, full), v);
        assert_eq!(ExtractBits::extract_bits(v, full), v);
    }
    for_both_carriers!(body);
}
