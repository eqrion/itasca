# Compiler construction proofs

Compilation constructs syntactic relations between independent source syntax
and emitted slot code. It does not assume interpreter correctness. Read the
public [Compilation interface](../../Results/Definitions/Compiler/Compilation.lean#L261) and
[Compile results](../../Results/Compile.lean) for the certificate and premises.

Dependency stages are strict:

- `Local/` proves individual emissions, callback effects, lowering and bounds.
- `Body/` combines reader replay, operand/control relations and structured body
  traversal into function and initializer certificates.
- `Module/` assembles entry parsing, scheduling, finishing and module certificates.

Local cannot import Body or Module; Body cannot import Module. The same stages
apply to public definition owners. Shared representation and source-capacity
vocabulary stays below its compiler constructions. Compiler modules must not
transitively import extracted interpreter functions. The
[runtime guide](../README.md#compiler-stages) explains the certificate families.
