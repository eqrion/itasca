# Working on itasca

Before changing Rust or Lean, read the [public guarantees and trust boundary](README.md#formal-verification). Flag changes to a public theorem, its premises, or a trusted model in the change description.

- Edit Rust in `src/`. After a change to extracted code, run `just extract` from `lean/` and review the generated diff. `FunsExternal.lean` is the handwritten model for external operations.
- Change the generated Wasm specification through its pinned inputs and patches. The [Lean workspace guide](lean/README.md) gives the regeneration commands.
- Proofs may depend only on `propext`, `Classical.choice`, and `Quot.sound`. Never add axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcuts, or kernel bypasses.

For proof changes, follow the [proof engineering guide](lean/PROOF_ENGINEERING.md).
