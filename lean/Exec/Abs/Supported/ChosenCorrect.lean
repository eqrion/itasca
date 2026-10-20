import Exec.Abs.Cumulative.ChosenCorrect
import Exec.Abs.Supported.Language
namespace Exec.Abs.Supported
open Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ next := by
  cases covered with
  | cumulative allowed => exact Cumulative.instruction_chosen_simulation admissible vector occurrence s ambient f rest op after next allowed typed equation
  | external impossible => rw [impossible] at equation; contradiction
  | block bt body =>
    exact ChosenNextSim.single admissible (chosen_typed_block_simulation admissible vector occurrence s ambient f rest after bt body next typed.typed equation)
  | loop bt body =>
    exact ChosenNextSim.single admissible (chosen_typed_loop_simulation admissible vector occurrence s ambient f rest after bt body next typed.typed equation)
  | ifelse bt yes no =>
    exact chosen_core_if_simulation admissible vector occurrence s ambient f rest bt yes no after next typed.typed equation



/-- Every successful mutable Core step is source typed and source simulated;
ordinary and mutable instructions share the same active/suspended-frame model. -/
theorem step_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s next : AState) (typed : CoreTyped s) (covered : SupportedState allowed s)
    (heads : ∀ {op}, allowed op → CoreHead op)
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
        exact instruction_chosen_simulation admissible vector occurrence source ambient frame rest op after next (heads (body op (by simp))) typed equation

end Exec.Abs.Supported
