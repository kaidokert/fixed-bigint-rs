use crate::harness::*;

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

// Both carriers must expose the identical shift/bitwise operand matrix:
// receiver ∈ {value, `&`}, RHS ∈ {usize, u32, &usize, &u32} for the shift
// operators and their assigns, `Not` on `&Self`, and the `Bit*Assign<&Self>`
// forms. The `where`-clause is the contract — if either carrier is missing a
// form this fails to compile for that instantiation. The extra bounds live
// here rather than on `Carrier` so the value-`usize`-only bare literals in the
// other tests stay unambiguous.
#[test]
#[allow(clippy::op_ref)]
fn shift_bitwise_operand_forms() {
    fn body<C>()
    where
        C: Carrier + Shl<u32, Output = C> + Shr<u32, Output = C> + ShlAssign<u32> + ShrAssign<u32>,
        for<'a> C: Shl<&'a usize, Output = C>
            + Shl<&'a u32, Output = C>
            + Shr<&'a usize, Output = C>
            + Shr<&'a u32, Output = C>
            + ShlAssign<&'a usize>
            + ShlAssign<&'a u32>
            + ShrAssign<&'a usize>
            + ShrAssign<&'a u32>
            + BitAndAssign<&'a C>
            + BitOrAssign<&'a C>
            + BitXorAssign<&'a C>,
        for<'a> &'a C: Not<Output = C>
            + Shl<usize, Output = C>
            + Shl<u32, Output = C>
            + Shl<&'a usize, Output = C>
            + Shl<&'a u32, Output = C>
            + Shr<usize, Output = C>
            + Shr<u32, Output = C>
            + Shr<&'a usize, Output = C>
            + Shr<&'a u32, Output = C>,
    {
        let a = C::from_u32(0x1234_5678);
        let b = C::from_u32(0x0F0F_0F0F);
        let su: usize = 5;
        let s3: u32 = 5;

        // Every `<<` operand form equals the value/usize form.
        let l = a << su;
        assert_eq!(a << &su, l);
        assert_eq!(a << s3, l);
        assert_eq!(a << &s3, l);
        assert_eq!(&a << su, l);
        assert_eq!(&a << &su, l);
        assert_eq!(&a << s3, l);
        assert_eq!(&a << &s3, l);

        // Same for `>>`.
        let r = a >> su;
        assert_eq!(a >> &su, r);
        assert_eq!(a >> s3, r);
        assert_eq!(a >> &s3, r);
        assert_eq!(&a >> su, r);
        assert_eq!(&a >> &su, r);
        assert_eq!(&a >> s3, r);
        assert_eq!(&a >> &s3, r);

        // `Not` on `&Self` matches the value form.
        assert_eq!(!&a, !a);

        // Assign forms agree with the operator.
        let mut x = a;
        x <<= s3;
        assert_eq!(x, l);
        let mut x = a;
        x <<= &su;
        assert_eq!(x, l);
        let mut x = a;
        x <<= &s3;
        assert_eq!(x, l);
        let mut x = a;
        x >>= s3;
        assert_eq!(x, r);
        let mut x = a;
        x >>= &su;
        assert_eq!(x, r);
        let mut x = a;
        x >>= &s3;
        assert_eq!(x, r);

        // `Bit*Assign<&Self>` matches the value-RHS assign.
        let mut x = a;
        x &= &b;
        assert_eq!(x, a & b);
        let mut x = a;
        x |= &b;
        assert_eq!(x, a | b);
        let mut x = a;
        x ^= &b;
        assert_eq!(x, a ^ b);
    }
    for_both_carriers!(body);
}

#[test]
fn shift_family() {
    fn body<C: Carrier>() {
        let v = C::from_u32(1);
        // overflowing / wrapping / checked keyed on amount vs 32-bit width.
        assert_eq!(
            OverflowingShl::overflowing_shl(v, 4),
            (C::from_u32(16), false)
        );
        assert_eq!(OverflowingShl::overflowing_shl(v, 32), (v, true));
        assert_eq!(OverflowingShr::overflowing_shr(v, 32), (v, true));
        assert_eq!(WrappingShl::wrapping_shl(v, 32), v);
        assert_eq!(
            WrappingShr::wrapping_shr(C::from_u32(16), 2),
            C::from_u32(4)
        );
        assert_eq!(CheckedShl::checked_shl(v, 5), Some(C::from_u32(32)));
        assert_eq!(CheckedShl::checked_shl(v, 32), None);
        assert_eq!(CheckedShr::checked_shr(v, 32), None);

        // unbounded saturates to zero past the width.
        assert_eq!(
            UnboundedShl::unbounded_shl(C::from_u32(0xFF), 100),
            C::from_u32(0)
        );
        assert_eq!(
            UnboundedShr::unbounded_shr(C::from_u32(0xFF), 100),
            C::from_u32(0)
        );

        // exact shifts: lossless only.
        assert_eq!(
            ShrExact::shr_exact(C::from_u32(0b100), 2),
            Some(C::from_u32(1))
        );
        assert_eq!(ShrExact::shr_exact(C::from_u32(0b100), 3), None);
        assert_eq!(ShlExact::shl_exact(v, 32), None);

        // funnel over the 32-bit pair.
        let hi = C::from_u32(0x1234_5678);
        let lo = C::from_u32(0x9ABC_DEF0);
        assert_eq!(FunnelShl::funnel_shl(hi, lo, 8), C::from_u32(0x3456_789A));
        assert_eq!(FunnelShr::funnel_shr(hi, lo, 8), C::from_u32(0x789A_BCDE));
    }
    for_both_carriers!(body);
}
