import Itasca.Runtime.Code.Local.Capacity.EmitAvailability
import Itasca.Runtime.Code.Local.Capacity.ObserveAvailability
import Itasca.Runtime.Code.Local.Lowering.Common.NumericOperands
import Itasca.Runtime.Code.Local.Lowering.Float.FloatOperands

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Numeric demand at a callback boundary. These are independent size,
coordinate, and budget bounds, not callback acceptance or code certificates. -/
structure CallbackDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop where
  pc : compiler.function.code.length ≤ U32.max
  codeCapacity : compiler.function.code.length < Usize.max
  sourceCapacity : compiler.function.source_offsets.length < Usize.max
  codeReserve : compiler.function.code.length + 1 ≤ bound
  sourceReserve : compiler.function.source_offsets.length + 1 ≤ bound
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  instruction : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

end Itasca.Runtime.Code
