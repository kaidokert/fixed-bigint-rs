//! Negative controls. Each fixture here exercises an Nct-side primitive
//! that has well-known data-dependent control flow. The driver runs the
//! same disassembly + grep on these and asserts each produces **at least
//! one** forbidden mnemonic. If a negative control produces zero
//! violations, the harness itself is broken — the most likely causes:
//!
//! - The compiler unexpectedly inlined the body away or constant-folded
//!   through black_box (unlikely but possible after a major rustc bump).
//! - The forbidden-mnemonic regex table for this target is missing the
//!   spelling produced here (e.g., LLVM uses `.n` suffix but the regex
//!   only matches without it).
//! - The symbol got stripped by linker GC.
//!
//! Three controls cover three independent failure axes:
//!   - `nct_div`: long-division (per-bit comparison branches)
//!   - `nct_ilog10`: magnitude-bound while-loop with `>=` comparisons
//!   - `nct_gcd`: Stein's algorithm — magnitude-comparing branches
//!     plus secret-dependent shift-by-trailing-zeros
//!
//! All three are guaranteed to emit conditional branches on any target
//! we care about. If any of them passes the gate, fix the gate.

use const_num_traits::Nct;
use fixed_bigint::FixedUInt;

use crate::ct_fix_bin;

// =============================================================================
// nct_div: long division. Per-bit dispatch in `const_div_rem`.
// =============================================================================

macro_rules! emit_nct_div {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Nct>::from(a);
            let y = FixedUInt::<$T, $N, Nct>::from(b);
            // Guard against /0 panic — the fixture body itself isn't on
            // a hot path; we just need codegen.
            let safe = if y == FixedUInt::<$T, $N, Nct>::from([0; $N]) {
                FixedUInt::<$T, $N, Nct>::from([1; $N])
            } else {
                y
            };
            let r = x / safe;
            *r.words()
        });
    };
}
emit_nct_div!(nct_fix__neg__nct_div__u32__N4, u32, 4);
emit_nct_div!(nct_fix__neg__nct_div__u32__N16, u32, 16);

// =============================================================================
// nct_ilog10: while (n >= 10) { n /= 10; count += 1; } — magnitude-bound
// loop plus `>=` comparison on a value derived from input.
// =============================================================================

#[no_mangle]
pub extern "C" fn nct_fix__neg__nct_ilog10__u32__N4(a_ptr: *const [u32; 4]) -> u32 {
    use const_num_traits::Ilog10;
    let a_arr = core::hint::black_box(unsafe { *a_ptr });
    let x = FixedUInt::<u32, 4, Nct>::from(a_arr);
    // ilog10 panics on zero — guard with a safe value.
    let safe = if x == FixedUInt::<u32, 4, Nct>::from([0u32; 4]) {
        FixedUInt::<u32, 4, Nct>::from([1u32; 4])
    } else {
        x
    };
    let result = Ilog10::ilog10(safe);
    core::hint::black_box(result)
}

// =============================================================================
// nct_gcd: Stein's algorithm. Subtraction + comparison loop.
// =============================================================================

macro_rules! emit_nct_gcd {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            use fixed_bigint::num_integer::Integer;
            // Guard the gcd(0, _) case AND emit a data-dependent branch
            // inside the fixture body itself. Integer::gcd's actual
            // implementation lives in a separate helper symbol; this
            // guard ensures the wrapper has visible forbidden mnemonics
            // regardless of whether the helper call is on the
            // driver's scan list.
            let zero: [$T; $N] = [0; $N];
            let one: [$T; $N] = [1; $N];
            if a == zero || b == zero {
                *FixedUInt::<$T, $N, Nct>::from(one).words()
            } else {
                let x = FixedUInt::<$T, $N, Nct>::from(a);
                let y = FixedUInt::<$T, $N, Nct>::from(b);
                let r = Integer::gcd(&x, &y);
                *r.words()
            }
        });
    };
}
emit_nct_gcd!(nct_fix__neg__nct_gcd__u32__N4, u32, 4);
