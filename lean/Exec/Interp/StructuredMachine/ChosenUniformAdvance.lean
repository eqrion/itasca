import Exec.Interp.StructuredMachine.ChosenAdvance
import Exec.Interp.Machines.Uniform.UniformControl
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- The existing mutable advance, with the same endpoint and a uniform silent rank. -/
def ChosenUniformAdvance (choices : Spec.SourceChoices) (occurrence : Nat) (emission : FunctionEmission) (supported : Abs.AState → Prop)
    (owned : Abs.Ownership.Bounds → Abs.AState → Prop) {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution emission supported view code store exec after expected nextPC nextPending ∧
    ChosenConcreteSim choices occurrence codeLength pc nextPC pending nextPending before after ∧
    UniformConcreteSim pc nextPC pending nextPending before after [] ∧
    (∀ bounds, owned bounds before → owned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

variable {choices : Spec.SourceChoices} {occurrence : Nat} {emission supported owned} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}

theorem ChosenUniformAdvance.forget
    (step : ChosenUniformAdvance choices occurrence emission supported owned view code store exec expected codeLength pc pending before) :
    ChosenAdvance choices occurrence emission supported owned view code store exec expected codeLength pc pending before := by
  obtain ⟨nextPC,nextPending,after,machine,simulation,uniform,ownership,ambient,bounded⟩ := step
  exact ⟨nextPC,nextPending,after,machine,simulation,ownership,ambient,bounded⟩

theorem ChosenUniformAdvance.of_frame_forward (admissible : choices.Admissible) {nextPC : Aeneas.Std.U32} {after : Abs.AState}
    (machine : Execution emission supported view code store exec after expected nextPC.val false)
    (simulation : ChosenConcreteSim choices occurrence codeLength pc nextPC.val false false before after)
    (forward : pc < nextPC.val)
    (ownership : ∀ bounds, owned bounds before → owned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    ChosenUniformAdvance choices occurrence emission supported owned view code store exec expected codeLength pc false before :=
  ⟨nextPC.val,false,after,machine,simulation,
    (simulation.erases admissible).uniform_forward forward (by scalar_tac),ownership,ambient,bounded⟩

theorem ChosenUniformAdvance.of_frame_pending {nextPC : Aeneas.Std.U32}
    (machine : Execution emission supported view code store exec before expected nextPC.val false) :
    ChosenUniformAdvance choices occurrence emission supported owned view code store exec expected codeLength pc true before :=
  ⟨nextPC.val,false,before,machine,Or.inl ⟨rfl,dispatchMeasure_jump _ _ _ _⟩,
    .pending _ _ _,fun _ h => h,rfl,fun _ h => h⟩

theorem ChosenUniformAdvance.of_frame_positive (admissible : choices.Admissible) {nextPC : Aeneas.Std.U32} {nextPending : Bool} {after : Abs.AState} {count : Nat}
    (machine : Execution emission supported view code store exec after expected nextPC.val nextPending)
    (positive : 0 < count) (steps : Spec.ChosenStepsN choices occurrence count (Abs.decode before) [] (Abs.decode after))
    (ownership : ∀ bounds, owned bounds before → owned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    ChosenUniformAdvance choices occurrence emission supported owned view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,Or.inr ⟨count,positive,steps⟩,
    .of_steps positive (steps.erases admissible),ownership,ambient,bounded⟩
end Exec.Interp.StructuredMachine
