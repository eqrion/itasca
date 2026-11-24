# Individual compiler effects

Local proofs describe a callback, emitted instruction, lowered operand or control
update before composing a complete instruction body. Source prefixes and typed
source traces supply independent input evidence. Emission relations, auxiliary
tables and stack/control layout describe the resulting compiler state.

`Lowering/` proves instruction effects. `Callbacks/` tracks compiler callback
state; `Relations/` composes stack, control, table and operand certificates.
`Coordinates/`, `Checking/` and `Publication/` track source offsets, instruction
checks and final published ranges. `Demand/` and `Capacity/` turn source demand
and allocator availability into successful operations.

Public certificate definitions are under
[Results/Definitions/Compiler/Local](../../../Results/Definitions/README.md).
This stage cannot import compiler Body or Module, including through public definitions.
It also cannot depend on extracted interpreter functions. The
[Body stage](../Body/README.md) composes these local effects; shared representation
lemmas belong below both.
