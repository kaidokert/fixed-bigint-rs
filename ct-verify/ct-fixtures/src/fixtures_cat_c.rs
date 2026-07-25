//! Category C: methods that are always CT-by-construction (generic over
//! P) — fixed-N limb loops, no operand-dependent branches. We exercise
//! them under `Ct` here as a regression watch: if a future LLVM
//! optimization or refactor introduces a data-dependent branch into one
//! of these "obviously CT" bodies, the harness catches it.

use core::ops::{BitAnd, BitOr, BitXor, Not};

use const_num_traits::Ct;
use const_num_traits::{
    BorrowingSub, CarryingAdd, CarryingMul, Midpoint, OverflowingAdd, OverflowingMul,
    OverflowingSub, PrimBits, WrappingAdd, WrappingMul, WrappingSub,
};
use fixed_bigint::FixedUInt;

use crate::{ct_fix_bin, ct_fix_count, ct_fix_un};

// =============================================================================
// Bitwise: Not / BitAnd / BitOr / BitXor
// =============================================================================

macro_rules! emit_not {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_un!($name, crate::catalog::not, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_not!(ct_fix__C__not__u8__N16, u8, 16);
emit_not!(ct_fix__C__not__u32__N4, u32, 4);
emit_not!(ct_fix__C__not__u32__N16, u32, 16);
emit_not!(ct_fix__C__not__u64__N4, u64, 4);

macro_rules! emit_bitand {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::bitand, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_bitand!(ct_fix__C__bitand__u8__N16, u8, 16);
emit_bitand!(ct_fix__C__bitand__u32__N4, u32, 4);
emit_bitand!(ct_fix__C__bitand__u32__N16, u32, 16);
emit_bitand!(ct_fix__C__bitand__u64__N4, u64, 4);

macro_rules! emit_bitor {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::bitor, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_bitor!(ct_fix__C__bitor__u8__N16, u8, 16);
emit_bitor!(ct_fix__C__bitor__u32__N4, u32, 4);
emit_bitor!(ct_fix__C__bitor__u32__N16, u32, 16);
emit_bitor!(ct_fix__C__bitor__u64__N4, u64, 4);

macro_rules! emit_bitxor {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::bitxor, FixedUInt<$T, $N, Ct>, $T, $N);
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
            let (r, _ov) = OverflowingAdd::overflowing_add(&x, &y);
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
        crate::emit_wl_bin!($name, crate::catalog::wrapping_mul, FixedUInt<$T, $N, Ct>, $T, $N);
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
        // of `CarryingAdd::carrying_add` itself. We pass the bool
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
            let (r, co) = CarryingAdd::carrying_add(x, y, c);
            let result = core::hint::black_box(*r.words());
            unsafe {
                *out_ptr = result;
            }
            core::hint::black_box(co as u8)
        }
        #[cfg(feature = "ctgrind")]
        fbx_ctgrind_carrying_add!($name, $T, $N);
    };
}
emit_carrying_add!(ct_fix__C__carrying_add__u8__N16, u8, 16);
emit_carrying_add!(ct_fix__C__carrying_add__u32__N4, u32, 4);
emit_carrying_add!(ct_fix__C__carrying_add__u32__N16, u32, 16);
emit_carrying_add!(ct_fix__C__carrying_add__u64__N4, u64, 4);

// Borrowing sub — the CT counterpart of `carrying_add`; identical ABI
// (a, b, borrow) → (out, borrow_out), so it reuses the carrying_add shape.
macro_rules! emit_borrowing_sub {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            borrow: bool,
            out_ptr: *mut [$T; $N],
        ) -> u8 {
            let a_arr = core::hint::black_box(unsafe { *a_ptr });
            let b_arr = core::hint::black_box(unsafe { *b_ptr });
            let bin = core::hint::black_box(borrow);
            let x = FixedUInt::<$T, $N, Ct>::from(a_arr);
            let y = FixedUInt::<$T, $N, Ct>::from(b_arr);
            let (r, bo) = BorrowingSub::borrowing_sub(x, y, bin);
            let result = core::hint::black_box(*r.words());
            unsafe {
                *out_ptr = result;
            }
            core::hint::black_box(bo as u8)
        }
        #[cfg(feature = "ctgrind")]
        fbx_ctgrind_carrying_add!($name, $T, $N);
    };
}
emit_borrowing_sub!(ct_fix__C__borrowing_sub__u8__N16, u8, 16);
emit_borrowing_sub!(ct_fix__C__borrowing_sub__u32__N4, u32, 4);
emit_borrowing_sub!(ct_fix__C__borrowing_sub__u32__N16, u32, 16);
emit_borrowing_sub!(ct_fix__C__borrowing_sub__u64__N4, u64, 4);

// Regression-watch bins — always-CT by construction (no `P::TAG` split), but
// pinned so a future change can't silently introduce a branch. Overflowing
// forms discard the flag; the body's branch-freeness is what's scanned.
macro_rules! emit_wrapping_add {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::wrapping_add, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_wrapping_add!(ct_fix__C__wrapping_add__u8__N16, u8, 16);
emit_wrapping_add!(ct_fix__C__wrapping_add__u32__N4, u32, 4);
emit_wrapping_add!(ct_fix__C__wrapping_add__u64__N4, u64, 4);

macro_rules! emit_wrapping_sub {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::wrapping_sub, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_wrapping_sub!(ct_fix__C__wrapping_sub__u8__N16, u8, 16);
emit_wrapping_sub!(ct_fix__C__wrapping_sub__u32__N4, u32, 4);
emit_wrapping_sub!(ct_fix__C__wrapping_sub__u64__N4, u64, 4);

macro_rules! emit_overflowing_sub {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::overflowing_sub, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_overflowing_sub!(ct_fix__C__overflowing_sub__u8__N16, u8, 16);
emit_overflowing_sub!(ct_fix__C__overflowing_sub__u32__N4, u32, 4);
emit_overflowing_sub!(ct_fix__C__overflowing_sub__u64__N4, u64, 4);

macro_rules! emit_overflowing_mul {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::overflowing_mul, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_overflowing_mul!(ct_fix__C__overflowing_mul__u8__N16, u8, 16);
emit_overflowing_mul!(ct_fix__C__overflowing_mul__u32__N4, u32, 4);
emit_overflowing_mul!(ct_fix__C__overflowing_mul__u64__N4, u64, 4);

// Widening carrying mul — `(a, b, carry) → (lo, hi)`. Pins the full-width
// carry-propagation tail of the schoolbook multiply *directly*, not just
// transitively through wrapping/saturating mul. Two array outputs (lo, hi).
macro_rules! emit_carrying_mul {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            carry_ptr: *const [$T; $N],
            lo_ptr: *mut [$T; $N],
            hi_ptr: *mut [$T; $N],
        ) {
            let a = core::hint::black_box(unsafe { *a_ptr });
            let b = core::hint::black_box(unsafe { *b_ptr });
            let cy = core::hint::black_box(unsafe { *carry_ptr });
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let cin = FixedUInt::<$T, $N, Ct>::from(cy);
            let (lo, hi) = CarryingMul::carrying_mul(x, y, cin);
            unsafe {
                *lo_ptr = core::hint::black_box(*lo.words());
                *hi_ptr = core::hint::black_box(*hi.words());
            }
        }
        #[cfg(feature = "ctgrind")]
        fbx_ctgrind_carrying_mul!($name, $T, $N);
    };
}
emit_carrying_mul!(ct_fix__C__carrying_mul__u8__N16, u8, 16);
emit_carrying_mul!(ct_fix__C__carrying_mul__u32__N4, u32, 4);
emit_carrying_mul!(ct_fix__C__carrying_mul__u32__N16, u32, 16);
emit_carrying_mul!(ct_fix__C__carrying_mul__u64__N4, u64, 4);

// =============================================================================
// Midpoint
// =============================================================================

macro_rules! emit_midpoint {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_bin!($name, crate::catalog::midpoint, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_midpoint!(ct_fix__C__midpoint__u8__N16, u8, 16);
emit_midpoint!(ct_fix__C__midpoint__u32__N4, u32, 4);
emit_midpoint!(ct_fix__C__midpoint__u32__N16, u32, 16);
emit_midpoint!(ct_fix__C__midpoint__u64__N4, u64, 4);

// =============================================================================
// Bit counts: count_ones / swap_bytes / reverse_bits
// =============================================================================

macro_rules! emit_count_ones {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_count!($name, crate::catalog::count_ones, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_count_ones!(ct_fix__C__count_ones__u8__N16, u8, 16);
emit_count_ones!(ct_fix__C__count_ones__u32__N4, u32, 4);
emit_count_ones!(ct_fix__C__count_ones__u32__N16, u32, 16);
emit_count_ones!(ct_fix__C__count_ones__u64__N4, u64, 4);

macro_rules! emit_swap_bytes {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_un!($name, crate::catalog::swap_bytes, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_swap_bytes!(ct_fix__C__swap_bytes__u8__N16, u8, 16);
emit_swap_bytes!(ct_fix__C__swap_bytes__u32__N4, u32, 4);
emit_swap_bytes!(ct_fix__C__swap_bytes__u32__N16, u32, 16);
emit_swap_bytes!(ct_fix__C__swap_bytes__u64__N4, u64, 4);

macro_rules! emit_reverse_bits {
    ($name:ident, $T:ty, $N:literal) => {
        crate::emit_wl_un!($name, crate::catalog::reverse_bits, FixedUInt<$T, $N, Ct>, $T, $N);
    };
}
emit_reverse_bits!(ct_fix__C__reverse_bits__u8__N16, u8, 16);
emit_reverse_bits!(ct_fix__C__reverse_bits__u32__N4, u32, 4);
emit_reverse_bits!(ct_fix__C__reverse_bits__u32__N16, u32, 16);
emit_reverse_bits!(ct_fix__C__reverse_bits__u64__N4, u64, 4);
