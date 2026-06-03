//! Non-Linux stubs. Lets cargo build succeed; actual verification is
//! Linux-only because Valgrind doesn't run elsewhere.

pub fn is_under_valgrind() -> bool {
    false
}

pub fn count_errors() -> usize {
    0
}

pub fn mark_undefined(_addr: *const u8, _len: usize) {}

pub fn mark_defined(_addr: *const u8, _len: usize) {}
