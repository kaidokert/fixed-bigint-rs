//! Category C: methods that are always CT-by-construction (generic over
//! P) — fixed-N limb loops, no operand-dependent branches. We exercise
//! them under `Ct` here as a regression watch: if a future LLVM
//! optimization or refactor introduces a data-dependent branch into one
//! of these "obviously CT" bodies, the harness catches it.

use core::ops::{BitAnd, BitOr, BitXor, Not};

use fixed_bigint::const_numtraits::{
    ConstBitPrimInt, ConstCarryingAdd, ConstMidpoint, ConstOverflowingAdd, ConstWrappingMul,
};
use fixed_bigint::{Ct, FixedUInt};

use crate::{ct_fix_bin, ct_fix_count, ct_fix_un};

// =============================================================================
// Bitwise: Not / BitAnd / BitOr / BitXor
// =============================================================================

macro_rules! emit_not {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = Not::not(x);
            *r.words()
        });
    };
}
emit_not!(ct_fix__C__not__u8__N16, u8, 16);
emit_not!(ct_fix__C__not__u32__N4, u32, 4);
emit_not!(ct_fix__C__not__u32__N16, u32, 16);
emit_not!(ct_fix__C__not__u64__N4, u64, 4);

macro_rules! emit_bitand {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = BitAnd::bitand(x, y);
            *r.words()
        });
    };
}
emit_bitand!(ct_fix__C__bitand__u8__N16, u8, 16);
emit_bitand!(ct_fix__C__bitand__u32__N4, u32, 4);
emit_bitand!(ct_fix__C__bitand__u32__N16, u32, 16);
emit_bitand!(ct_fix__C__bitand__u64__N4, u64, 4);

macro_rules! emit_bitor {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = BitOr::bitor(x, y);
            *r.words()
        });
    };
}
emit_bitor!(ct_fix__C__bitor__u8__N16, u8, 16);
emit_bitor!(ct_fix__C__bitor__u32__N4, u32, 4);
emit_bitor!(ct_fix__C__bitor__u32__N16, u32, 16);
emit_bitor!(ct_fix__C__bitor__u64__N4, u64, 4);

macro_rules! emit_bitxor {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = BitXor::bitxor(x, y);
            *r.words()
        });
    };
}
emit_bitxor!(ct_fix__C__bitxor__u8__N16, u8, 16);
emit_bitxor!(ct_fix__C__bitxor__u32__N4, u32, 4);
emit_bitxor!(ct_fix__C__bitxor__u32__N16, u32, 16);
emit_bitxor!(ct_fix__C__bitxor__u64__N4, u64, 4);

// =============================================================================
// Overflowing / wrapping arithmetic (always-CT carry chain)
// =============================================================================

macro_rules! emit_overflowing_add {
    ($name:ident, $T:ty, $N:literal) => {
        // Overflowing returns (Self, bool). We discard the bool to keep
        // the ABI simple; the body's branch-freeness is what we check.
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let (r, _ov) = ConstOverflowingAdd::overflowing_add(&x, &y);
            *r.words()
        });
    };
}
emit_overflowing_add!(ct_fix__C__overflowing_add__u8__N16, u8, 16);
emit_overflowing_add!(ct_fix__C__overflowing_add__u32__N4, u32, 4);
emit_overflowing_add!(ct_fix__C__overflowing_add__u32__N16, u32, 16);
emit_overflowing_add!(ct_fix__C__overflowing_add__u64__N4, u64, 4);

macro_rules! emit_wrapping_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstWrappingMul::wrapping_mul(&x, &y);
            *r.words()
        });
    };
}
emit_wrapping_mul!(ct_fix__C__wrapping_mul__u8__N16, u8, 16);
emit_wrapping_mul!(ct_fix__C__wrapping_mul__u32__N4, u32, 4);
emit_wrapping_mul!(ct_fix__C__wrapping_mul__u32__N16, u32, 16);
emit_wrapping_mul!(ct_fix__C__wrapping_mul__u64__N4, u64, 4);

// =============================================================================
// Carrying add (ConstCarryingAdd) — explicit external carry input
// =============================================================================

macro_rules! emit_carrying_add {
    ($name:ident, $T:ty, $N:literal) => {
        // Take `bool` directly in the ABI. Going through `carry_in: u8`
        // and `!= 0` introduces a `cpi/brne` on AVR (no `setne`-style
        // instruction) — but that's a wrapper artifact, not a property
        // of `ConstCarryingAdd::carrying_add` itself. We pass the bool
        // straight through `black_box` so any branch the gate then
        // detects is inside the primitive, where it belongs.
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            carry: bool,
            out_ptr: *mut [$T; $N],
        ) -> u8 {
            let a_arr = core::hint::black_box(unsafe { *a_ptr });
            let b_arr = core::hint::black_box(unsafe { *b_ptr });
            let c = core::hint::black_box(carry);
            let x = FixedUInt::<$T, $N, Ct>::from(a_arr);
            let y = FixedUInt::<$T, $N, Ct>::from(b_arr);
            let (r, co) = ConstCarryingAdd::carrying_add(x, y, c);
            let result = core::hint::black_box(*r.words());
            unsafe {
                *out_ptr = result;
            }
            core::hint::black_box(co as u8)
        }
    };
}
emit_carrying_add!(ct_fix__C__carrying_add__u8__N16, u8, 16);
emit_carrying_add!(ct_fix__C__carrying_add__u32__N4, u32, 4);
emit_carrying_add!(ct_fix__C__carrying_add__u32__N16, u32, 16);
emit_carrying_add!(ct_fix__C__carrying_add__u64__N4, u64, 4);

// =============================================================================
// Midpoint
// =============================================================================

macro_rules! emit_midpoint {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstMidpoint::midpoint(x, y);
            *r.words()
        });
    };
}
emit_midpoint!(ct_fix__C__midpoint__u8__N16, u8, 16);
emit_midpoint!(ct_fix__C__midpoint__u32__N4, u32, 4);
emit_midpoint!(ct_fix__C__midpoint__u32__N16, u32, 16);
emit_midpoint!(ct_fix__C__midpoint__u64__N4, u64, 4);

// =============================================================================
// Bit counts: count_ones / count_zeros / swap_bytes / reverse_bits
// =============================================================================

macro_rules! emit_count_ones {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstBitPrimInt::count_ones(x)
        });
    };
}
emit_count_ones!(ct_fix__C__count_ones__u8__N16, u8, 16);
emit_count_ones!(ct_fix__C__count_ones__u32__N4, u32, 4);
emit_count_ones!(ct_fix__C__count_ones__u32__N16, u32, 16);
emit_count_ones!(ct_fix__C__count_ones__u64__N4, u64, 4);

macro_rules! emit_swap_bytes {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = ConstBitPrimInt::swap_bytes(x);
            *r.words()
        });
    };
}
emit_swap_bytes!(ct_fix__C__swap_bytes__u8__N16, u8, 16);
emit_swap_bytes!(ct_fix__C__swap_bytes__u32__N4, u32, 4);
emit_swap_bytes!(ct_fix__C__swap_bytes__u32__N16, u32, 16);
emit_swap_bytes!(ct_fix__C__swap_bytes__u64__N4, u64, 4);

macro_rules! emit_reverse_bits {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = ConstBitPrimInt::reverse_bits(x);
            *r.words()
        });
    };
}
emit_reverse_bits!(ct_fix__C__reverse_bits__u8__N16, u8, 16);
emit_reverse_bits!(ct_fix__C__reverse_bits__u32__N4, u32, 4);
emit_reverse_bits!(ct_fix__C__reverse_bits__u32__N16, u32, 16);
emit_reverse_bits!(ct_fix__C__reverse_bits__u64__N4, u64, 4);
