import Exec.Abs.Core.Run
import Exec.Abs.Core.ChosenCorrect
import Exec.Abs.Core.ChosenTerminal
namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Actual finite Core runs keep one fixed policy. The occurrence of each
next chunk is determined by the preceding checked source reduction count. -/
theorem Run.chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {n : Nat} {s last : AState}
    (run : Run n s last) (typed : CoreTyped s) (covered : CoreState s) :
    ∃ count, ChosenStepsN choices occurrence count (decode s) [] (decode last) := by
  induction run generalizing occurrence with
  | refl state => exact ⟨0,.refl occurrence typed.typed.decode_wf⟩
  | @next state middle last n equation run ih =>
    have middleTyped := (step_correct state middle typed covered equation).1
    have middleCore := step_core state middle typed.typed covered equation
    rcases step_chosen_simulation admissible vector occurrence state middle typed covered equation with
      ⟨same,_⟩ | ⟨first,_,head⟩
    · obtain ⟨count,tail⟩ := ih occurrence middleTyped middleCore
      exact ⟨count,same.symm ▸ tail⟩
    · obtain ⟨count,tail⟩ := ih (occurrence+first) middleTyped middleCore
      exact ⟨first+count,by simpa only [List.nil_append] using head.trans tail⟩

theorem Run.chosen_done {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {n : Nat} {s last : AState}
    (run : Run n s last) (typed : CoreTyped s) (covered : CoreState s) (values : List val)
    (done : step last = .done values) :
    ∃ count, ChosenStepsN choices occurrence count (decode s) [] ⟨⟨last.store,last.ambient⟩,vals values⟩ := by
  obtain ⟨count,source⟩ := run.chosen admissible vector occurrence typed covered
  exact ⟨count,done_simulation last values done ▸ source⟩

theorem Run.chosen_trap {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {n : Nat} {s last : AState}
    (run : Run n s last) (typed : CoreTyped s) (covered : CoreState s) (trapped : step last = .trap) :
    ∃ count, 0<count ∧ ChosenStepsN choices occurrence count (decode s) [] ⟨⟨last.store,last.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨before,source⟩ := run.chosen admissible vector occurrence typed covered
  obtain ⟨lastTyped,lastCore,_,_⟩ := run.correct typed covered
  obtain ⟨after,positive,trap⟩ := step_chosen_trap admissible vector (occurrence+before) last lastTyped lastCore trapped
  exact ⟨before+after,by omega,by simpa only [List.nil_append] using source.trans trap⟩
end Exec.Abs.Core
