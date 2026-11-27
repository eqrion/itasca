# Host steps and Wasm builtins

[Host](Host.lean) extends generated reduction with atomic host returns and traps. Each host step records a direct event and requires store extension and a well-typed final store, including when the callback commits effects before trapping. A reentrant invocation has its own trace.

The [builtin inventory](Builtins/Inventory.lean) classifies the domains and permitted outcomes of builtins defined by the [SpecTec output patch](../../../patches/spectec-wasm2-builtins.patch). The [integer representation proofs](Builtins/IntegerRepresentation.lean) and [float proofs](Builtins/Float/) establish properties of those definitions.
