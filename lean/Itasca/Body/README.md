# Instruction-body validation proofs

This layer connects the mutable operand/control stacks to independently encoded
instruction trees and declarative typing. Public body certificates, cursor/stack
invariants and grammar witnesses live under
[Interface body definitions](../Results/Definitions/README.md).

The argument has three directions:

- Soundness restores the body invariant after each returning instruction step,
  then turns a closed final state into encoding and typing evidence.
- Normal-return proofs bound readers, stacks and the validation loop even when
  the remaining bytes are malformed or a callback rejects.
- Completeness starts with independent encoding and typing, constructs successful
  instruction execution, and composes it through structured blocks and the loop.

`Body.Scalar/`, `Body.Control/`, `References/`, `Bulk/`, `NumericExt/` and `Simd/` separate
instruction families. `Step/` joins their cases; `Trace/` and `Visitor/` retain
observations and exact byte/callback correspondence. `Complete/ScalarBase` holds
shared concrete-frame and scalar completeness lemmas used by the unified proof;
it is proof decomposition, not a supported language subset or profile.

Code-entry proofs consume the finished body certificate. Body validation uses
validator functions and stays independent of runtime implementation proofs and
SpecExt, including through public definitions.
