import Exec.Abs.Core.Pure
import Exec.Abs.Sim.Step
import Exec.Abs.Core.PureMetadata
import Exec.Abs.Core.MemoryLoad
import Exec.Abs.Core.MemoryStore

import Exec.Abs.Core.Control

namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Every successful covered instruction preserves source store/frame typing
and has a counted source simulation (or the bounded constant stutter). -/
theorem instruction_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ next := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | slice allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped] at equation
    refine ⟨⟨Exec.Abs.instruction_preservation s ambient f rest _ after next allowed typed.typed equation,?_⟩,
      Exec.Abs.instruction_simulation s ambient f rest _ after next allowed typed.typed equation⟩
    simpa only [astep_store equation] using typed.contents
  | constant ty value =>
    obtain ⟨actual,actualEq,fresh,simulation⟩ := constant_progress s ambient f rest after ty value typed
    rw [actualEq] at equation
    cases equation
    exact ⟨fresh,simulation⟩
  | select =>
    obtain ⟨actual,actualEq,fresh,simulation⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ = .next next at equation
    rw [actualEq] at equation
    cases equation
    exact ⟨fresh,.single simulation⟩
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,simulation⟩ := globalGet_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,extension,simulation⟩ := globalSet_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
  | load op argument =>
    rw [instruction_load] at equation
    rcases load_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
    · rw [actualEq] at equation
      contradiction
  | store op argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,extension,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
    · rw [actualEq] at equation
      contradiction
  | block bt body _ =>
    have pure : astep ⟨s,ambient,{f with code := .BLOCK bt body :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨block_preservation s ambient f rest after bt body next typed.typed pure,?_⟩,
      typed_block_simulation s ambient f rest after bt body next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents
  | loop bt body _ =>
    have pure : astep ⟨s,ambient,{f with code := .LOOP bt body :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨loop_preservation s ambient f rest after bt body next typed.typed pure,?_⟩,
      typed_loop_simulation s ambient f rest after bt body next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents
  | ifelse bt yes no _ _ =>
    have pure : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨core_if_preservation s ambient f rest bt yes no after next typed.typed pure,?_⟩,
      core_if_simulation s ambient f rest bt yes no after next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents

theorem empty_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := []} :: rest,[]⟩)
    (equation : astep ⟨s,ambient,{f with code := []} :: rest,[]⟩ = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := []} :: rest,[]⟩ next := by
  have contents : StoreContentsTyped next.store := by simpa only [astep_store equation] using typed.contents
  cases f with
  | mk address resultTypes locals module labels code values =>
    let frame : AFrame := ⟨address,resultTypes,locals,module,labels,[],values⟩
    have frameTyped : FrameTyped s frame [] := by
      cases typed.typed.frames with | cons head _ => exact head
    cases labels with
    | nil =>
      have valuesTyped := frame_end_typed (f := frame) frameTyped
      change ResultsTyped s resultTypes values at valuesTyped
      have count := resultsTyped_length valuesTyped
      have returned : ResultsTyped s resultTypes (values.drop (values.length-resultTypes.length)) := by
        simpa only [count,Nat.sub_self,List.drop_zero] using valuesTyped
      exact ⟨⟨returnFrame_preservation typed.typed returned equation,contents⟩,
        .single (typed_frame_end_simulation s ambient frame rest next typed.typed equation)⟩
    | cons label labels =>
      have simulation := typed_label_end_simulation s ambient frame rest label labels next typed.typed equation
      refine ⟨⟨?_,contents⟩,simulation⟩
      simp only [astep] at equation
      split at equation
      · simp only [advance,AResult.next.injEq] at equation
        rw [← equation]
        exact active_frame_preservation typed.typed (label_exit_frame_preservation (f := frame) frameTyped) rfl
      · contradiction

/-- Every successful mutable Core step is source typed and source simulated;
ordinary and mutable instructions share the same active/suspended-frame model. -/
theorem step_correct (s next : AState) (typed : CoreTyped s) (covered : CoreState s)
    (equation : step s = .next next) : CoreTyped next ∧ NextSim s next := by
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
      | nil => exact empty_correct source ambient frame rest next typed equation
      | cons op after =>
        exact instruction_correct source ambient frame rest op after next (body op (by simp)) typed equation

end Exec.Abs.Core
