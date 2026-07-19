//! Deliberately-panicky fixtures for the shared panic-audit self-test.

use core::hint::black_box;

#[unsafe(no_mangle)]
pub extern "C" fn panic_audit__neg__bounds_check(index: usize, out: *mut u8) {
    if out.is_null() {
        return;
    }
    let values = black_box([0u8; 4]);
    let value = values[black_box(index)];
    unsafe { *out = black_box(value) };
}

#[unsafe(no_mangle)]
pub extern "C" fn panic_audit__neg__unwrap(out: *mut u8) {
    if out.is_null() {
        return;
    }
    let value = black_box(None::<u8>).unwrap();
    unsafe { *out = black_box(value) };
}

#[unsafe(no_mangle)]
pub extern "C" fn panic_audit__neg__expect(out: *mut u8) {
    if out.is_null() {
        return;
    }
    let value = black_box(None::<u8>).expect("panic audit negative control");
    unsafe { *out = black_box(value) };
}
