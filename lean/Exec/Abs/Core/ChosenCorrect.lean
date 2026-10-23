import Exec.Abs.Sim.ChosenBasic
import Exec.Abs.Core.Correct
import Exec.Abs.Sim.ChosenStep
namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Mutable Core transitions retain the selected policy, including source
control reductions and ordinary scalar memory reads and writes. -/
theorem instruction_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (op : instr) (after : List instr) (next : AState) (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after}::rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := op :: after}::rest,[]⟩ next := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | pure allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped] at equation
    exact chosen_instruction_simulation admissible vector occurrence s ambient f rest _ after next allowed typed.typed equation
  | const ty value =>
    simp only [instruction,advance,AResult.next.injEq] at equation
    rw [←equation]
    exact .inl ⟨decode_const s ambient f rest ty value after (by simpa only [FrameHeights] using frameTyped_heights frameTyped),
      const_measure_decreases s ambient f rest ty value after⟩
  | select =>
    obtain ⟨actual,actualEq,fresh,simulation⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ = .next next at equation
    rw [actualEq] at equation
    cases equation
    exact ChosenNextSim.neutral admissible vector occurrence simulation (by simp only [List.map_cons,admininstr_instr,neutralActive])
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,simulation⟩ := globalGet_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ChosenNextSim.neutral admissible vector occurrence simulation (by simp only [List.map_cons,admininstr_instr,neutralActive])
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,extension,simulation⟩ := globalSet_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ChosenNextSim.neutral admissible vector occurrence simulation (by simp only [List.map_cons,admininstr_instr,neutralActive])
  | load op argument =>
    rw [instruction_load] at equation
    rcases load_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ChosenNextSim.neutral admissible vector occurrence simulation (by simp only [List.map_cons,Memory.Load.source,admininstr_instr,neutralActive])
    · rw [actualEq] at equation
      contradiction
  | store op argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,extension,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ChosenNextSim.neutral admissible vector occurrence simulation (by simp only [List.map_cons,Memory.Store.source,admininstr_instr,neutralActive])
    · rw [actualEq] at equation
      contradiction

theorem empty_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := []}::rest,[]⟩)
    (equation : astep ⟨s,ambient,{f with code := []}::rest,[]⟩ = .next next) :
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := []}::rest,[]⟩ next := by
  cases f with
  | mk address resultTypes locals module labels code values =>
    let frame : AFrame := ⟨address,resultTypes,locals,module,labels,[],values⟩
    cases labels with
    | nil =>
      exact ChosenNextSim.neutral admissible vector occurrence
        (typed_frame_end_simulation s ambient frame rest next typed.typed equation)
        (by simp only [frame,List.map_nil,neutralActive])
    | cons label labels =>
      exact chosen_typed_label_end_simulation admissible vector occurrence s ambient frame rest label labels next typed.typed equation

end Exec.Abs.Core
