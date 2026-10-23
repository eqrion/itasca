import Exec.Abs.Core.ChosenCorrect
import Exec.Abs.Supported.CoreStuck
namespace Exec.Abs.Supported
open Exec.Abs.Core
open SpecExt Exec.Spec

/-- Every successful mutable Core step is source typed and source simulated;
ordinary and mutable instructions share the same active/suspended-frame model. -/
theorem step_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s next : AState) (typed : CoreTyped s) (covered : SupportedState s)
    (equation : step s = .next next) : ChosenNextSim choices occurrence s next := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have body := (covered.active frame (by simp)).1
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | nil => exact empty_chosen_simulation admissible vector occurrence source ambient frame rest next typed equation
      | cons op after =>
        rcases BinaryInstr.core_head (body op (by simp)) with head | stuck
        · exact Core.instruction_chosen_simulation admissible vector occurrence source ambient frame rest op after next head typed equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation

end Exec.Abs.Supported
