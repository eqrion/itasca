import Exec.Abs.Core.Correct
import Exec.Abs.Core.ChosenControl
import Exec.Abs.Sim.ChosenStep
namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Mutable Core transitions retain the selected policy, including source
control reductions and ordinary scalar memory reads and writes. -/
theorem instruction_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (op : instr) (after : List instr) (next : AState) (covered : CoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after}::rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := op :: after}::rest,[]⟩ next := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | slice allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped] at equation
    exact chosen_instruction_simulation admissible vector occurrence s ambient f rest _ after next allowed typed.typed equation
  | constant ty value =>
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
  | block bt body _ =>
    exact ChosenNextSim.single admissible (chosen_typed_block_simulation admissible vector occurrence s ambient f rest after bt body next typed.typed equation)
  | loop bt body _ =>
    exact ChosenNextSim.single admissible (chosen_typed_loop_simulation admissible vector occurrence s ambient f rest after bt body next typed.typed equation)
  | ifelse bt yes no _ _ =>
    exact chosen_core_if_simulation admissible vector occurrence s ambient f rest bt yes no after next typed.typed equation

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

theorem step_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s next : AState)
    (typed : CoreTyped s) (covered : CoreState s) (equation : step s = .next next) :
    ChosenNextSim choices occurrence s next := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.typed.activeResults (by simp)
    change results=[] at noResults
    subst results
    have body := (covered.active frame (by simp)).1
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | nil => exact empty_chosen_simulation admissible vector occurrence source ambient frame rest next typed equation
      | cons op after => exact instruction_chosen_simulation admissible vector occurrence source ambient frame rest op after next (body op (by simp)) typed equation
end Exec.Abs.Core
