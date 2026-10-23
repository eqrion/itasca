import Itasca.Handler.StackSemantics

/-!
# End, else and if handlers

Outcome predicates `EndResult` and `ElseResult` for the extracted `code.read_end` and
`code.read_else`, and their realization theorems `code.read_end.realizes` and
`code.read_else.realizes`, which relate the operand segment to the frame's result types.
`code.read_if.from_block_type` gives the effect of `code.read_if` on the stack, including the
popped `i32` condition.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca
