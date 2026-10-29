import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.SourceMachine.Sim.Step
import Itasca.Runtime.SourceMachine.Core.PureMetadata
import Itasca.Runtime.SourceMachine.Core.MemoryAccess


namespace Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

/-- Every successful covered instruction preserves source store/frame typing
and has a counted source simulation (or the bounded constant stutter). -/
theorem instruction_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ next := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | pure allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped] at equation
    refine ⟨⟨Itasca.Runtime.Abs.instruction_preservation s ambient f rest _ after next allowed typed.typed equation,?_⟩,
      Itasca.Runtime.Abs.instruction_simulation s ambient f rest _ after next allowed typed.typed equation⟩
    simpa only [astep_store equation] using typed.contents
  | const ty value =>
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

end Itasca.Runtime.Abs.Core
