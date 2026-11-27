# Following an execution proof

| Guarantee | Where the proof comes together |
| --- | --- |
| Compilation | The [compiler](Compiler/README.md) joins local emissions, function bodies, and module assembly to relate emitted slot code to source syntax. |
| Instantiation | The [store proofs](Store/README.md) resolve imports, stage allocations, initialize segments, and identify the start function. |
| Invocation | The [interpreter](Interp/README.md) relates machine steps to the [flat source machine](SourceMachine/README.md), whose decoding recovers SpecTec configurations. |

[Integration](Integration/README.md) constructs a store invariant that satisfies the [public runtime protocol](../Results/Definitions/Runtime.lean). This is where the three guarantees meet: later invocations can rely on code and store facts established by earlier operations, including across host calls.
