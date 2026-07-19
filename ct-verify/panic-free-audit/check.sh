#!/bin/sh
# Panic-free audit: cross-build the audit staticlib and assert no panic
# machinery was synthesized into the reviewed entry points.
set -eu

TARGET="${1:-thumbv7m-none-eabi}"
HOST="$(rustc -vV | sed -n 's/^host: //p')"
NM="$(rustc --print sysroot)/lib/rustlib/${HOST}/bin/llvm-nm"
TARGET_DIR="${CARGO_TARGET_DIR:-target}"
ARCHIVE="${TARGET_DIR}/${TARGET}/release/libpanic_free_audit.a"

if [ ! -x "$NM" ]; then
    echo "error: llvm-nm not found at $NM (install llvm-tools-preview)" >&2
    exit 2
fi

cargo build --release -p panic-free-audit --target "$TARGET"

if [ ! -f "$ARCHIVE" ]; then
    echo "error: panic audit archive not found at $ARCHIVE" >&2
    exit 2
fi

FOUND="$("$NM" "$ARCHIVE" | grep -E 'core9panicking|panic_fmt|unwrap_failed|expect_failed|panic_bounds_check|slice_(start|end)_index' || true)"
if [ -n "$FOUND" ]; then
    echo "panic machinery found in ${ARCHIVE}:" >&2
    echo "$FOUND" >&2
    exit 1
fi

echo "OK: no panic symbols in ${ARCHIVE}"
