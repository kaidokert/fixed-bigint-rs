//! Linux implementation — real crabgrind calls.

use std::ffi::c_void;

pub fn is_under_valgrind() -> bool {
    !matches!(crabgrind::run_mode(), crabgrind::RunMode::Native)
}

pub fn count_errors() -> usize {
    crabgrind::count_errors()
}

pub fn mark_undefined(addr: *const u8, len: usize) {
    let _ = crabgrind::memcheck::mark_mem(
        addr as *mut c_void,
        len,
        crabgrind::memcheck::MemState::Undefined,
    );
}

pub fn mark_defined(addr: *const u8, len: usize) {
    let _ = crabgrind::memcheck::mark_mem(
        addr as *mut c_void,
        len,
        crabgrind::memcheck::MemState::Defined,
    );
}
