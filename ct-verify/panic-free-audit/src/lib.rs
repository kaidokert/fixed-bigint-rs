//! Linker-DCE audit fixtures for `FixedUInt` byte serialisation.
//!
//! Each `#[no_mangle] pub extern "C"` symbol exercises one byte-
//! conversion method at one type instantiation. After cross-building for
//! an embedded target with the workspace's release profile
//! (lto=fat, codegen-units=1, opt-level=z, panic=abort), `cargo nm` on
//! the resulting `.a` should report no `panic_*` / `unwind` symbols
//! traced back to these methods.
//!
//! Two call paths × three shape combinations:
//!
//! - Paths: the explicit `to_{le,be}_bytes_fixed` (const-asserted
//!   buffer size) and the `num_traits::ToBytes` trait path (routes
//!   through `holder_be`/`holder_le`).
//! - Shapes: `FixedUInt<u32, 8>` (256-bit / Curve25519), plus
//!   `FixedUInt<u8, 256>` and `FixedUInt<u64, 32>` (2048-bit RSA-scale
//!   moduli at both extremes of the word-stride range).
//!
//! The RSA-scale shapes are included because stable rustc through MSRV
//! does not fold `copy_from_slice`'s length assert for those
//! monomorphizations; auditing them here locks the byte-wise zip loop
//! down against regressions to a `copy_from_slice`-shaped inner copy.
//!
//! `black_box` at every boundary so the optimizer can't fold inputs
//! through and DCE the body wholesale (same hygiene as ct-fixtures).

#![no_std]
#![allow(non_snake_case)]

#[cfg(feature = "neg-controls")]
mod neg_controls;

#[cfg(feature = "diagnostic-ct-scans")]
use const_num_traits::{Ct, PrimBits};
use core::hint::black_box;
use fixed_bigint::{FixedUInt, HeaplessBigInt};

type U256 = FixedUInt<u32, 8>; // 32-byte / 256-bit, Curve25519-shaped

// ── Ct branchless scans (shared `const_cmp_ct` / `const_leading_zeros_ct` /
//    `const_trailing_zeros_ct`) ──
//
// These moved from `&[T; N]` to `&[T]` so both carriers share one copy of the
// `black_box`-guarded loop; lock down that the slice signature stays
// panic-free at both carriers (the array length is compile-time on FixedUInt;
// heapless passes `&limbs[..n]` with `n <= CAP` by invariant).

#[cfg(feature = "diagnostic-ct-scans")]
type U256Ct = FixedUInt<u32, 8, Ct>;
#[cfg(feature = "diagnostic-ct-scans")]
type HeaplessU256Ct = HeaplessBigInt<u32, 8, Ct>;

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__fixed_cmp_ct(a: u32, b: u32) -> i32 {
    let x = U256Ct::from(black_box(a));
    let y = U256Ct::from(black_box(b));
    black_box(x.cmp(&y) as i32)
}

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__fixed_leading_zeros_ct(a: u32) -> u32 {
    let x = U256Ct::from(black_box(a));
    black_box(PrimBits::leading_zeros(x))
}

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__heapless_cmp_ct(a: u32, b: u32) -> i32 {
    let x = HeaplessU256Ct::from(black_box(a));
    let y = HeaplessU256Ct::from(black_box(b));
    black_box(x.cmp(&y) as i32)
}

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__heapless_leading_zeros_ct(a: u32) -> u32 {
    let x = HeaplessU256Ct::from(black_box(a));
    black_box(PrimBits::leading_zeros(x))
}

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__fixed_trailing_zeros_ct(a: u32) -> u32 {
    let x = U256Ct::from(black_box(a));
    black_box(PrimBits::trailing_zeros(x))
}

#[cfg(feature = "diagnostic-ct-scans")]
#[no_mangle]
pub extern "C" fn panic_audit__heapless_trailing_zeros_ct(a: u32) -> u32 {
    let x = HeaplessU256Ct::from(black_box(a));
    black_box(PrimBits::trailing_zeros(x))
}

#[no_mangle]
pub extern "C" fn panic_audit__to_le_bytes_fixed(seed: u32, out: *mut [u8; 32]) {
    // `from_array` is pub(crate), so we construct via the public `From<u32>`
    // and let the value live in only the low limb. This still routes through
    // `to_le_bytes_fixed`'s full body — the byte-width math doesn't depend
    // on the value, just on the type parameters.
    let v = U256::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_le_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__to_be_bytes_fixed(seed: u32, out: *mut [u8; 32]) {
    let v = U256::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_be_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__from_le_bytes_fixed(bytes: *const [u8; 32], out: *mut [u32; 8]) {
    let buf = black_box(unsafe { &*bytes });
    let v: U256 = U256::from_le_bytes_fixed(buf);
    let arr = black_box(*v.words());
    unsafe { *out = arr };
}

#[no_mangle]
pub extern "C" fn panic_audit__from_be_bytes_fixed(bytes: *const [u8; 32], out: *mut [u32; 8]) {
    let buf = black_box(unsafe { &*bytes });
    let v: U256 = U256::from_be_bytes_fixed(buf);
    let arr = black_box(*v.words());
    unsafe { *out = arr };
}

// ── `HeaplessBigInt::from_{le,be}_bytes` (delegate to `impl_from_*_bytes_slice`) ──
//
// Same byte→limb helper as the `from_*_bytes_fixed` fixtures above; these
// lock down that `HeaplessBigInt`'s decode (oversize guard + `div_ceil` len
// + the shared scatter) stays panic-free at the Curve25519 shape and at the
// RSA-scale u8/256 shape where the length-assert fold historically failed.

type HeaplessU256 = HeaplessBigInt<u32, 8>;
type HeaplessU2048B = HeaplessBigInt<u8, 256>;

#[no_mangle]
pub extern "C" fn panic_audit__heapless_from_le_bytes(bytes: *const [u8; 32], out: *mut [u32; 8]) {
    let buf = black_box(unsafe { &*bytes });
    let v: HeaplessU256 = HeaplessBigInt::from_le_bytes(buf);
    let arr = black_box(*v.all_limbs());
    unsafe { *out = arr };
}

#[no_mangle]
pub extern "C" fn panic_audit__heapless_from_be_bytes(bytes: *const [u8; 32], out: *mut [u32; 8]) {
    let buf = black_box(unsafe { &*bytes });
    let v: HeaplessU256 = HeaplessBigInt::from_be_bytes(buf);
    let arr = black_box(*v.all_limbs());
    unsafe { *out = arr };
}

#[no_mangle]
pub extern "C" fn panic_audit__heapless_from_le_bytes__u8_256(
    bytes: *const [u8; 256],
    out: *mut [u8; 256],
) {
    let buf = black_box(unsafe { &*bytes });
    let v: HeaplessU2048B = HeaplessBigInt::from_le_bytes(buf);
    let arr = black_box(*v.all_limbs());
    unsafe { *out = arr };
}

#[no_mangle]
pub extern "C" fn panic_audit__heapless_from_be_bytes__u8_256(
    bytes: *const [u8; 256],
    out: *mut [u8; 256],
) {
    let buf = black_box(unsafe { &*bytes });
    let v: HeaplessU2048B = HeaplessBigInt::from_be_bytes(buf);
    let arr = black_box(*v.all_limbs());
    unsafe { *out = arr };
}

// ── `num_traits::ToBytes` at U256 (routes through `holder_be`/`_le`) ──

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_be_bytes__u32_8(seed: u32, out: *mut [u8; 32]) {
    let v = U256::from(black_box(seed));
    let bytes = <U256 as num_traits::ToBytes>::to_be_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), 32) };
    let _ = black_box(unsafe { &*out });
}

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_le_bytes__u32_8(seed: u32, out: *mut [u8; 32]) {
    let v = U256::from(black_box(seed));
    let bytes = <U256 as num_traits::ToBytes>::to_le_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), 32) };
    let _ = black_box(unsafe { &*out });
}

// ── 2048-bit RSA-scale shapes ────────────────────────────────────────

type U2048u8 = FixedUInt<u8, 256>;
type U2048u64 = FixedUInt<u64, 32>;
const RSA_BYTE_WIDTH: usize = 256;

#[no_mangle]
pub extern "C" fn panic_audit__to_le_bytes_fixed__u8_256(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u8::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_le_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__to_be_bytes_fixed__u8_256(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u8::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_be_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_be_bytes__u8_256(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u8::from(black_box(seed));
    let bytes = <U2048u8 as num_traits::ToBytes>::to_be_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), RSA_BYTE_WIDTH) };
    let _ = black_box(unsafe { &*out });
}

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_le_bytes__u8_256(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u8::from(black_box(seed));
    let bytes = <U2048u8 as num_traits::ToBytes>::to_le_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), RSA_BYTE_WIDTH) };
    let _ = black_box(unsafe { &*out });
}

#[no_mangle]
pub extern "C" fn panic_audit__to_le_bytes_fixed__u64_32(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u64::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_le_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__to_be_bytes_fixed__u64_32(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u64::from(black_box(seed));
    let buf = unsafe { &mut *out };
    let written = v.to_be_bytes_fixed(buf);
    let _ = black_box(written);
}

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_be_bytes__u64_32(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u64::from(black_box(seed));
    let bytes = <U2048u64 as num_traits::ToBytes>::to_be_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), RSA_BYTE_WIDTH) };
    let _ = black_box(unsafe { &*out });
}

#[no_mangle]
pub extern "C" fn panic_audit__num_traits_to_le_bytes__u64_32(
    seed: u32,
    out: *mut [u8; RSA_BYTE_WIDTH],
) {
    let v = U2048u64::from(black_box(seed));
    let bytes = <U2048u64 as num_traits::ToBytes>::to_le_bytes(&v);
    let src: &[u8] = bytes.as_ref();
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (*out).as_mut_ptr(), RSA_BYTE_WIDTH) };
    let _ = black_box(unsafe { &*out });
}

// ── HasNonZero/DivNonZero panic-deletion audit ───────────────────────
//
// Tests whether `div_nonzero` / `rem_nonzero` survive DCE without
// dragging in `panic_fmt` from `FixedUInt`'s `Div`/`Rem` zero check.
// The trait contract guarantees `d != 0`, but the underlying
// `FixedUInt::Div` impl still has a runtime zero check internally —
// the open question is whether LLVM proves it unreachable through the
// `NonZeroFixedUInt` wrapper. Same DCE question as `*_bytes_fixed`.

#[cfg(feature = "diagnostic-nonzero-div")]
use const_num_traits::{DivNonZero, HasNonZero, Nct};
#[cfg(feature = "diagnostic-nonzero-div")]
use fixed_bigint::NonZeroFixedUInt;

#[cfg(feature = "diagnostic-nonzero-div")]
type U256Nct = FixedUInt<u32, 8, Nct>;

#[cfg(feature = "diagnostic-nonzero-div")]
#[no_mangle]
pub extern "C" fn panic_audit__div_nonzero(seed_a: u32, seed_m: u32, out: *mut [u32; 8]) {
    let a = U256Nct::from(black_box(seed_a));
    let m = U256Nct::from(black_box(seed_m));
    // `into_nonzero().unwrap()` retains a panic site on its own, but
    // that's the *construction* path. We want to audit whether the
    // `div_nonzero` *consumption* path retains a zero-check panic.
    // Hoist construction outside the audit point via a hint that the
    // unwrap is unreachable for non-zero `seed_m` — opt for the
    // closer-to-real-consumer shape: caller has already constructed
    // the proof and passes it in.
    let nz: NonZeroFixedUInt<u32, 8, Nct> = match m.into_nonzero() {
        Some(nz) => nz,
        // Sentinel: in real consumer code, `into_nonzero` is at the
        // trust boundary (m known non-zero from a prior check). The
        // audit's point is the `div_nonzero` body, not the unwrap.
        None => return,
    };
    let q = <U256Nct as DivNonZero>::div_nonzero(a, nz);
    let arr = black_box(*q.words());
    unsafe { *out = arr };
}

#[cfg(feature = "diagnostic-nonzero-div")]
#[no_mangle]
pub extern "C" fn panic_audit__rem_nonzero(seed_a: u32, seed_m: u32, out: *mut [u32; 8]) {
    let a = U256Nct::from(black_box(seed_a));
    let m = U256Nct::from(black_box(seed_m));
    let nz: NonZeroFixedUInt<u32, 8, Nct> = match m.into_nonzero() {
        Some(nz) => nz,
        None => return,
    };
    let r = <U256Nct as DivNonZero>::rem_nonzero(a, nz);
    let arr = black_box(*r.words());
    unsafe { *out = arr };
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
