# Platform-law proofs and witnesses

Public allocator, memory, floating-point, interrupt and host contracts are exposed
through [Interface/Platform](../../Results/Definitions/Platform.lean#L176) and
[HostContracts](../../Results/Definitions/Runtime.lean#L33). This layer proves
law preservation/erasure and concrete satisfiability witnesses, including
[VecMemory](VecMemory.lean) and [FloatWitness](FloatWitness.lean).

These witnesses establish the stated Lean models. They do not prove that native
Rust wrappers satisfy all generic laws. Public execution theorems retain those
laws as explicit premises; keep that distinction when documenting witnesses.
