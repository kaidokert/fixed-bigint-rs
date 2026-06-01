//! Thin abstraction over crabgrind's Valgrind client requests.
//!
//! crabgrind links against Valgrind's C headers, which aren't available
//! outside Linux (Valgrind itself doesn't support macOS aarch64 or Windows).
//! On non-Linux hosts this module compiles as no-op stubs so the workspace
//! still builds, but actually exercising the gate requires Linux.

#[cfg(target_os = "linux")]
mod real;

#[cfg(target_os = "linux")]
pub use real::*;

#[cfg(not(target_os = "linux"))]
mod stub;

#[cfg(not(target_os = "linux"))]
pub use stub::*;
