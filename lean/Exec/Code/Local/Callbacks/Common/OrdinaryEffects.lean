import Exec.Code.Local.Callbacks.Common.FixupPreservation
import Exec.Code.Local.Capacity.AuxiliaryGrowth
import Exec.Code.Local.Capacity.CapacityHelpers

/-!
What every compiler callback preserves when it emits code without opening,
closing or branching to a structured frame.
-/

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

structure OrdinaryEffects {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) : Prop where
  tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function
  depths : after.table_depths = before.table_depths
  code_mono : before.function.code.val.length ≤ after.function.code.val.length
  stable : CompilerOrdinaryStable before after
  capacity : CapacityStep before after state

theorem OrdinaryEffects.fixups {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} (effects : OrdinaryEffects before after state) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length :=
  fun budget => budget.ordinary effects.stable effects.code_mono

theorem OrdinaryEffects.auxiliary_growth {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} (effects : OrdinaryEffects before after state) : AuxiliaryGrowth before after :=
  .of_tables effects.tables effects.code_mono

end Exec.Code
