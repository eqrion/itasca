# Complete-module compiler construction

This stage composes environment metadata, code-entry parsing, function and
initializer compilation, worker scheduling, successful finishing and output
collection. It joins body certificates with source ordering and decoded frame
capacities to establish the module-level syntactic correspondence.

[CompilationAvailable](BatchLoopAvailable.lean) constructs actual acceptance
from independent source validity, conservative source demand and bounded allocator
availability. [CompileTotal](Compilation.lean) proves normal return on arbitrary
bytes under allocator correctness. Normal return may produce a Rust error;
completeness supplies the stronger source and availability premises.

The public premises live in
[Results/Definitions/Compiler/Module](../../../Results/Definitions/README.md).
[Integration/Compilation](../../Integration/Compilation.lean) packages
module construction into the public certificate; [Results/Compile](../../../Results/Compile.lean)
states the guarantees. Module may import Local and Body, while both lower stages
remain independent of it. This stage also stays independent of extracted
interpreter functions.
