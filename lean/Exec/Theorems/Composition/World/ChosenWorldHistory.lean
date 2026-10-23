import Exec.Theorems.Composition.World.ChosenWorld
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
theorem ChosenWorld.history_erases {choices M P F A memory hooks floats allocator view expected before after n events}
    (history : Iterations (ChosenWorldTransition choices (M:=M) (P:=P) (F:=F) (A:=A)
      memory hooks floats allocator (view:=view) (expected:=expected)) n before events after) :
    Iterations (WorldRecordedTransition memory hooks floats allocator) n before.toEventfulWorld events after.toEventfulWorld := by
  induction history with
  | refl => exact .refl _
  | cons edge tail ih => exact .cons edge.recorded ih

theorem ChosenWorld.history_source {choices M P F A memory hooks floats allocator view expected before after n events}
    (history : Iterations (ChosenWorldTransition choices (M:=M) (P:=P) (F:=F) (A:=A)
      memory hooks floats allocator (view:=view) (expected:=expected)) n before events after) :
    ∃ count, after.occurrence=before.occurrence+count ∧
      ChosenStepsN choices before.occurrence count (Abs.decode before.machine.source) events (Abs.decode after.machine.source) := by
  induction history with
  | refl state => exact ⟨0,(Nat.add_zero _).symm,.refl _ state.machine.invariant.typed.typed.decode_wf⟩
  | @cons n before middle after firstEvents rest edge tail ih =>
    obtain ⟨count,clock,source⟩ := ih
    rcases edge.selected with ⟨same,sameClock,rfl,decrease⟩ | ⟨first,positive,advanced,head⟩
    · rw [sameClock] at clock source
      change Abs.decode before.machine.source=Abs.decode middle.machine.source at same
      rw [←same] at source
      exact ⟨count,clock,by simpa only [List.nil_append] using source⟩
    · rw [advanced] at clock source
      exact ⟨first+count,by simpa only [Nat.add_assoc] using clock,head.trans source⟩


end Exec.Theorems
