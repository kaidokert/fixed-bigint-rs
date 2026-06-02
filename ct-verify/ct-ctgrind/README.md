# ct-ctgrind

A second layer of CT verification for the same fixtures that `ct-driver`
inspects: instead of grepping disassembly for branches, this driver
runs each fixture under Valgrind with its input buffers tagged
`MAKE_MEM_UNDEFINED` via crabgrind. Valgrind then flags any
conditional jump or memory access that depends on those tainted
bytes — including the secret-derived loads (`table[secret & 0xf]`
and friends) that asm-grep can't see because they're not branches.
Between fixtures the driver reads Valgrind's error counter to
attribute violations to specific symbols, the same way the asm-grep
driver maps disassembled bodies back to fixture names. The same
negative-control fixtures from `ct-fixtures` are reused: every
`nct_fix__neg__*` symbol must trip Valgrind, or the harness itself
is broken.

To run it locally on a Linux host: `cargo build --release -p
ct-ctgrind && valgrind --tool=memcheck --error-exitcode=0 -q
target/release/ct-ctgrind`. Valgrind isn't available on macOS
aarch64 or Windows, so on those hosts the crate still compiles (via
no-op stubs in `src/valgrind/stub.rs`) but `cargo run -p ct-ctgrind`
just prints a "must be run under valgrind" error and exits. CI runs
the full gate on `x86_64-unknown-linux-gnu`. To extend the fixture
set, add the corresponding macro invocation in
`src/fixtures_cat_*.rs` and the matching `ct_fix_*!` entry in
`ct-fixtures` — the two files mirror each other one-for-one.
