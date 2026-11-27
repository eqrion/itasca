# WebAssembly validation specification

The generated `WebAssembly` module contains the Wasm 2.0 syntax, well-formedness, and typing judgments. See the [Lean workspace guide](../../README.md) for the pinned inputs and regeneration commands.

The [binary grammar](Binary/Module.lean) relates bytes to raw module syntax. Its [uniqueness theorem](Binary/ModuleUnique.lean) lives alongside the grammar.
