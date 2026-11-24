# Handwritten specification extensions

This foundation supplies host-aware source reduction and proofs about the pinned
specification's handwritten builtin definitions. It imports the generated
specification and upstream foundations, independently of the extracted runtime.
It belongs to the explicitly named foundations of the public execution claims.

[Host](Host.lean) defines `HostEvent`, `StepH` and `StepsH`: ordinary
generated reduction plus atomic typed host return/trap steps, with ordered direct
host events. Host transitions require store extension and a source-typed final
store, including when the host traps after committing effects. Reentrant Wasm
execution is subsumed by that host transition; a separate invocation has its own
trace. Runtime laws connect concrete callbacks to this source behavior.

[Inventory](Builtins/Inventory.lean) and the float modules under `Builtins/Float/`
check builtin properties; [IntegerRepresentation](Builtins/IntegerRepresentation.lean) proves the integer and lane
representation laws used by the extension. The actual builtin definitions are introduced by
the versioned specification patch, not opaque placeholders in this directory.
Changing those definitions requires source/patch regeneration and specification
checks; handwritten proof changes use the ordinary Lean checkpoint checks.
