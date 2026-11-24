# Interpreter operation and machine proofs

Operation-family proofs relate concrete slot/store effects to independent source
transitions. `Relations/` holds shared contracts; numeric, memory, state, SIMD,
control and call subjects prove their own cases. `Machine/` joins those cases into
the active/suspended frame relation and machine execution. `Invocation/` is the
final setup, run-loop, readback, event-recording and divergence stage.

Lower interpreter modules cannot import the final invocation stage. Public
machine and recording vocabulary lives under
[Interface](../../Results/Definitions/Runtime.lean#L1033); construction proofs stay here.
[Integration](../Integration/README.md) combines execution with the retained
executable-store invariant and host/resource premises. Public invocation claims
are in [Results/Invoke](../../Results/Invoke.lean).
