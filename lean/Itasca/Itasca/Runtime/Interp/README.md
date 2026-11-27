# From slot operations to invocation

Instruction-family proofs relate concrete slot and store updates to source transitions. [Machine](Machine/) composes them across active and suspended frames. [Invocation](Invocation/) handles entry, the run loop, result readback, and divergence. [Recording](Recording.lean) connects execution to the host events visible in the [public invocation guarantees](../../Results/Invoke.lean).
