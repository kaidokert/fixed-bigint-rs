# Local notes for working in this repo

This file is gitignored. It exists to keep working context out of the
public repo while still being on hand for Claude sessions.

## CT-verify harness

The `ct-verify/` workspace member ships a short README aimed at someone
who just wants to run the gate or copy the pattern into a downstream
crate. The full design notes — layered model, scope trade-offs, the
AVR `bool`/`u8` lesson, future pillars, file inventory — live in
`/CT_VERIFY.md` at this repo root (also gitignored). Read that before
making non-trivial changes to the harness; the trade-offs aren't
obvious from the code.
