# CI baseline probe (temporary)

This branch adds only this file on top of `origin/main`. Its sole purpose
is to fire the CI matrix — in particular the `nightly` leg's
`cargo test --features nightly` — to establish whether the released
`main` tree already fails on the `generic_const_exprs` path
(`FixedUInt::const_to_from_bytes` `E0275`), independent of any in-flight
`heapless-runtime-len` work. Delete once the question is answered.
