import Exec.Theorems.Composition.Supported.SupportedHistory
import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Spec.Choices.ChosenProgress
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The real host-free machine with its current source-reduction occurrence. -/
structure ChosenSupportedMachine (emission : StructuredMachine.FunctionEmission) (allowed : instr → Prop)
    (M P : Type) (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype)
    extends SupportedMachine emission allowed M P view code expected where
  occurrence : Nat

def ChosenSupportedMachine.potential {M P view code expected}
    (machine : ChosenSupportedMachine emission allowed M P view code expected) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

/-- Actual dispatch, metadata retention and a checked fixed-policy source
simulation. Native dispatch proofs below construct this evidence. -/
structure ChosenSupportedTransition (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : ChosenSupportedMachine emission allowed M P view code expected) (events : List HostEvent)
    (after : ChosenSupportedMachine emission allowed M P view code expected) : Prop where
  recorded : SupportedTransition memory hooks floats allocator before.toSupportedMachine events after.toSupportedMachine
  selected : ChosenDispatchSim choices (fun p : ChosenSupportedMachine emission allowed M P view code expected=>Abs.decode p.source)
    ChosenSupportedMachine.occurrence ChosenSupportedMachine.potential before events after

theorem ChosenSupportedTransition.empty {choices M P F A memory hooks floats allocator view code expected before events after}
    (edge : ChosenSupportedTransition (emission:=emission) (allowed:=allowed) choices (M:=M) (P:=P) (F:=F) (A:=A)
      memory hooks floats allocator (view:=view) (code:=code) (expected:=expected) before events after) : events=[] := edge.recorded.1

theorem ChosenSupportedMachine.history_erases {choices M P F A memory hooks floats allocator view code expected before after n events}
    (history : Iterations (ChosenSupportedTransition (emission:=emission) (allowed:=allowed) choices (M:=M) (P:=P) (F:=F) (A:=A)
      memory hooks floats allocator (view:=view) (code:=code) (expected:=expected)) n before events after) :
    Iterations (SupportedTransition memory hooks floats allocator) n before.toSupportedMachine events after.toSupportedMachine := by
  induction history with
  | refl => exact .refl _
  | cons edge tail ih => exact .cons edge.recorded ih

theorem ChosenSupportedMachine.history_source {choices M P F A memory hooks floats allocator view code expected before after n events}
    (history : Iterations (ChosenSupportedTransition (emission:=emission) (allowed:=allowed) choices (M:=M) (P:=P) (F:=F) (A:=A)
      memory hooks floats allocator (view:=view) (code:=code) (expected:=expected)) n before events after) :
    ∃ count, after.occurrence=before.occurrence+count ∧
      ChosenStepsN choices before.occurrence count (Abs.decode before.source) events (Abs.decode after.source) := by
  induction history with
  | refl state => exact ⟨0,(Nat.add_zero _).symm,.refl _ state.invariant.typed.typed.decode_wf⟩
  | @cons n before middle after firstEvents rest edge tail ih =>
    obtain ⟨count,clock,source⟩ := ih
    rcases edge.selected with ⟨same,sameClock,rfl,decrease⟩ | ⟨first,positive,advanced,head⟩
    · rw [sameClock] at clock source
      change Abs.decode before.source=Abs.decode middle.source at same
      rw [←same] at source
      exact ⟨count,clock,by simpa only [List.nil_append] using source⟩
    · rw [advanced] at clock source
      exact ⟨first+count,by simpa only [Nat.add_assoc] using clock,head.trans source⟩

/-- One returned native step exposes its exact next clock or its existing
classified failure and current source store. -/
def ChosenSupportedStepResult (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : ChosenSupportedMachine emission allowed M P view code expected)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CumulativeStoreMutation view code before.store out.2.2.1 ∧
  match out.1 with
  | .Ok _ => ∃ after : ChosenSupportedMachine emission allowed M P view code expected,
      out=(.Ok (),after.exec,after.store,after.platform) ∧ ChosenSupportedTransition choices memory hooks floats allocator before [] after
  | .Err error => ChosenCumulativeFailure choices before.occurrence allocator hooks before.exec before.store before.platform before.source error ∧
      Store.decodeStore view code out.2.2.1=before.source.store

def ChosenSupportedStepOutcomes (choices : SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) : Prop :=
  ∀ before : ChosenSupportedMachine emission allowed M P view code expected, 0<before.exec.frames.length →
    runtime.interp.step memory hooks floats allocator before.exec before.store before.platform
      ⦃ out => ChosenSupportedStepResult choices memory hooks floats allocator before out ⦄
end Exec.Theorems
