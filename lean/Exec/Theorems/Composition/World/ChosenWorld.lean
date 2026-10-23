import Exec.Theorems.Composition.World.ChosenWorldSourceStep
import Exec.Spec.Choices.ChosenProgress
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- The current interpreted machine and exact selected source occurrence. -/
structure ChosenWorld
    (M P : Type) (view : M → Slice U8) (expected : List valtype)
    extends EventfulWorld M P view expected where
  occurrence : Nat

def ChosenWorld.potential {M P view expected} (world : ChosenWorld M P view expected) : Nat :=
  dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source

structure ChosenWorldTransition (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (before : ChosenWorld M P view expected) (events : List HostEvent)
    (after : ChosenWorld M P view expected) : Prop where
  recorded : WorldRecordedTransition memory hooks floats allocator before.toEventfulWorld events after.toEventfulWorld
  selected : ChosenDispatchSim choices (fun p : ChosenWorld M P view expected=>Abs.decode p.machine.source)
    ChosenWorld.occurrence ChosenWorld.potential before events after

def ChosenWorldStepResult (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype} (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (before : ChosenWorld M P view expected) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ after : ChosenWorld M P view expected,
      Inv after.code after.machine.store ∧ out=(.Ok (),after.machine.exec,after.machine.store,after.machine.platform) ∧
      ChosenWorldTransition choices memory hooks floats allocator before (stepHostEvents before.machine.exec before.machine.store out) after
  | .Err _ => ChosenWorldSourceStepResult choices before.occurrence (view:=view)
      memory hooks floats allocator Inv before.code expected before.machine.exec before.machine.store before.machine.platform
      before.machine.source before.machine.pc before.machine.pending out

def ChosenWorldStepOutcomes (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (expected : List valtype) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ before : ChosenWorld M P view expected, Inv before.code before.machine.store →
    0<before.machine.exec.frames.length → runtime.interp.step memory hooks floats allocator
      before.machine.exec before.machine.store before.machine.platform ⦃ out =>
      ChosenWorldStepResult choices memory hooks floats allocator Inv before out ⦄

theorem ChosenWorldSourceStepResult.chosen_bundle {choices : SourceChoices} (admissible : choices.Admissible)
    {M P F A memory hooks floats allocator view expected Inv}
    {before : ChosenWorld M P view expected} {out : EventfulDispatchResult M P}
    (result : ChosenWorldSourceStepResult choices before.occurrence (M:=M) (P:=P) (F:=F) (A:=A) (view:=view) memory hooks floats allocator Inv before.code expected
      before.machine.exec before.machine.store before.machine.platform before.machine.source before.machine.pc before.machine.pending out)
    (actual : runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform=.ok out) :
    ChosenWorldStepResult choices memory hooks floats allocator Inv before out := by
  cases status : out.1 with
  | Err error => simpa only [ChosenWorldStepResult,status] using result
  | Ok unit =>
    cases unit
    simp only [ChosenWorldSourceStepResult,status] at result
    simp only [ChosenWorldStepResult,status]
    obtain ⟨next,valid,same,simulation,extension,metadata,ambient,agrees⟩ := result
    have recorded : WorldRecordedTransition memory hooks floats allocator before.toEventfulWorld
        (stepHostEvents before.machine.exec before.machine.store out) next := by
      refine ⟨⟨actual.trans (congrArg Result.ok same),simulation.erases admissible,extension,metadata,ambient,agrees⟩,?_⟩
      rw [same]
    rcases simulation with ⟨equal,empty,decrease⟩ | ⟨count,positive,steps⟩
    · let after : ChosenWorld M P view expected := ⟨next,before.occurrence⟩
      exact ⟨after,valid,same,recorded,Or.inl ⟨equal,rfl,empty,decrease⟩⟩
    · let after : ChosenWorld M P view expected := ⟨next,before.occurrence+count⟩
      exact ⟨after,valid,same,recorded,Or.inr ⟨count,positive,rfl,steps⟩⟩
end Exec.Theorems
