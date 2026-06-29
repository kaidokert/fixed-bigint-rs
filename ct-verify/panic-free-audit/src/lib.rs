//! Linker-DCE audit fixture for `FixedUInt::*_bytes_fixed`.
//!
//! Each `#[no_mangle] pub extern "C"` symbol exercises one of the four
//! new panic-free byte-conversion methods at a representative
//! instantiation. After cross-building for an embedded target with the
//! workspace's release profile (lto=fat, codegen-units=1, opt-level=z,
//! panic=abort), `cargo nm` on the resulting `.a` should report no
//! `panic_*` / `unwind` symbols traced back to these methods.
//!
//! Picks a real-world-shaped instantiation: `FixedUInt<u32, 8>` ⇒
//! 32 bytes (a Curve25519-shaped scalar). The buffer size matches
//! `BYTE_WIDTH` exactly to exercise the equal-size hot path that
//! downstream `ed25519_heapless` cares about.
//!
//! `black_box` at every boundary so the optimizer can't fold inputs
//! through and DCE the body wholesale (same hygiene as ct-fixtures).

#![no_std]
#![allow(non_snake_case)]

use core::hint::black_box;
use fixed_bigint::FixedUInt;

type U256 = FixedUInt<u32, 8>; // 32-byte / 256-bit, Curve25519-shaped

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

// ── HasNonZero/DivNonZero panic-deletion audit ───────────────────────
//
// Tests whether `div_nonzero` / `rem_nonzero` survive DCE without
// dragging in `panic_fmt` from `FixedUInt`'s `Div`/`Rem` zero check.
// The trait contract guarantees `d != 0`, but the underlying
// `FixedUInt::Div` impl still has a runtime zero check internally —
// the open question is whether LLVM proves it unreachable through the
// `NonZeroFixedUInt` wrapper. Same DCE question as `*_bytes_fixed`.

use const_num_traits::{DivNonZero, HasNonZero, Nct};
use fixed_bigint::NonZeroFixedUInt;

type U256Nct = FixedUInt<u32, 8, Nct>;

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
