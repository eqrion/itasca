import Exec.Interp.StructuredMachine.ChosenAdvance
import Exec.Interp.Machines.Uniform.UniformControl
import Exec.Abs.Stateful.OwnershipStore
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- The existing mutable advance, with the same endpoint and a uniform silent rank. -/
def ChosenUniformAdvance (choices : Spec.SourceChoices) (occurrence : Nat)
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution view code store exec after expected nextPC nextPending ∧
    ChosenConcreteSim choices occurrence codeLength pc nextPC pending nextPending before after ∧
    UniformConcreteSim pc nextPC pending nextPending before after [] ∧
    (∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

variable {choices : Spec.SourceChoices} {occurrence : Nat}  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}

theorem ChosenUniformAdvance.forget
    (step : ChosenUniformAdvance choices occurrence view code store exec expected codeLength pc pending before) :
    ChosenAdvance choices occurrence view code store exec expected codeLength pc pending before := by
  obtain ⟨nextPC,nextPending,after,machine,simulation,uniform,ownership,ambient,bounded⟩ := step
  exact ⟨nextPC,nextPending,after,machine,simulation,ownership,ambient,bounded⟩

theorem ChosenUniformAdvance.of_frame_forward (admissible : choices.Admissible) {nextPC : Aeneas.Std.U32} {after : Abs.AState}
    (machine : Execution view code store exec after expected nextPC.val false)
    (simulation : ChosenConcreteSim choices occurrence codeLength pc nextPC.val false false before after)
    (forward : pc < nextPC.val)
    (ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    ChosenUniformAdvance choices occurrence view code store exec expected codeLength pc false before :=
  ⟨nextPC.val,false,after,machine,simulation,
    (simulation.erases admissible).uniform_forward forward (by scalar_tac),ownership,ambient,bounded⟩

end Exec.Interp.StructuredMachine
