import Exec.Code.Local.Capacity.ObserveBudgetAvailability
import Exec.Code.Local.Capacity.BudgetEffects
import Exec.Code.Local.Capacity.EmitAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Bounds for the map/frame allocations common to every scope opening. -/
structure ScopeDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop where
  pc : compiler.function.code.length ≤ U32.max
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  mapsCapacity : compiler.function.controls.length < Usize.max
  mapsReserve : compiler.function.controls.length + 1 ≤ bound
  framesCapacity : compiler.frames.length < Usize.max
  framesReserve : compiler.frames.length + 1 ≤ bound
  control : compiler.budget.controls.val < compiler.budget.limits.max_controls.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

end Exec.Code
