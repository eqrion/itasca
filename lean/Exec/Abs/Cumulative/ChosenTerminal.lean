import Exec.Abs.Core.Terminal
import Exec.Abs.Cumulative.Dispatch
import Exec.Abs.FloatCore.ChosenTerminal
import Exec.Abs.CumulativeState
namespace Exec.Abs.Cumulative
open Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_chosen_trap {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CumulativeInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .trap) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n (decode ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  cases covered with
  | core allowed => exact FloatCore.instruction_chosen_trap admissible vector occurrence s ambient f rest op after allowed typed equation
  | stateful op => rw [stateful_not_core] at equation; contradiction
  | indirect_call table type => rw [indirect_not_core] at equation; contradiction
  | block bt body _ =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | loop bt body _ =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | ifelse bt yes no _ _ =>
    simp only [instruction,astep,advance] at equation
    repeat' first | contradiction | split at equation


theorem step_chosen_trap {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : AState) (typed : CoreTyped s) (covered : CumulativeState s)
    (equation : step s = .trap) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n (decode s) [] ⟨⟨s.store,s.ambient⟩,[.TRAP]⟩ := by
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
      | cons op after => exact instruction_chosen_trap admissible vector occurrence source ambient frame rest op after (body op (by simp)) typed equation
      | nil =>
        simp only [step,astep,returnFrame,advance] at equation
        repeat' first | contradiction | split at equation

end Exec.Abs.Cumulative
