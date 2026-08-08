# Notes for coding agents

veriwasm is a WebAssembly 1.0 validator in Rust whose function-body validator
carries a machine-checked Coq proof. That makes it unlike a normal Rust repo in
ways that are easy to miss.

Read these first:

- **[DEVELOPMENT.md](DEVELOPMENT.md)**: how to work on the project.
- **[TRUST.md](TRUST.md)**: what the proofs claim and what they assume.

## The things that catch people out

**`src/` and `theories/` are coupled.** The Coq model in
`theories/Veriwasm_Types.v` and `theories/Veriwasm_Funs.v` is generated from the
Rust and committed. Any change to `src/` needs `just extract` to regenerate it
and `just prove` to re-check the proofs. A Rust change that compiles and passes
`cargo test` can still break the build.

**Never hand-edit the generated theories.** `Veriwasm_Types.v` and
`Veriwasm_Funs.v` are overwritten by `just extract`.
`theories/Veriwasm_FunsExternal.v` *is* hand-written despite the name.

**All of `src/` is in a restricted subset**, so idiomatic Rust is often wrong
here. No iterators, no closures, no `.clone()`, no bitwise operators, no range
indexing, no `String`, explicit loop counters. DEVELOPMENT.md has the full list
with reasons.

**Adding an axiom or a kernel bypass weakens the result.** Do not add `Axiom`,
`Admitted`, `Unset Guard Checking` or `Unset Positivity Checking` to work around
a hard proof. `just extract-check` fails the build on a bypass; a new axiom will
not fail anything, which is exactly why it needs a conversation first.

**Scratch files go in `$TMPDIR`, not `/tmp`.** `.claude/settings.json` runs
bash sandboxed, and the sandbox grants a remapped `$TMPDIR` but not bare `/tmp`.

## Before saying you are done

```bash
cargo test
just extract        # if src/ changed
just prove
just extract-check
```

`just trust` prints the assumption count per theorem. If a number moves, say so
and explain why; TRUST.md quotes the headline four.
