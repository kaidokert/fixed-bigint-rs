# ct-verify

A small cross-target asm-grep gate for the constant-time primitives in
`fixed-bigint`. The fixtures crate emits one `#[no_mangle] pub extern "C"`
symbol per `(operation, T, N)` instantiation we want to check, with
`core::hint::black_box` at both ends so the optimizer can't fold the
body away. The driver cross-builds that crate, disassembles the
resulting archive with `llvm-objdump`, and flags any forbidden
conditional control transfer it finds inside the fixture wrappers —
`b.<cond>` and friends on Thumb, `beq`/`bne`/... on RISC-V, `br<cc>`
and the skip-if-bit family on AVR, `b.<cond>`/`cbz`/`tbz` on AArch64,
`j<cc>` on x86-64. A handful of negative-control fixtures exercise
non-CT operations and are required to trip the gate — they're the
harness's self-test.

To run it: `cargo run --release -p ct-driver` checks the host target;
`--target <triple>` checks a cross target (you'll need the matching
`rustup target add` first, plus the `llvm-tools-preview` component for
`llvm-objdump`). `--list-targets` shows what's supported.

`cyccnt-hardware` complements the static and ctgrind gates with paired-input
DWT measurements on the J-Trace STM32F407VG. It covers the Cortex-M-relevant
`u32x8`, `u32x16`, and `u8x32` carriers and requires its deliberately
variable-time Nct controls to separate. See its README for run commands and
measurement policy.
