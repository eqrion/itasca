import Exec.Spec.Choices.PureChoiceCoverage
import Exec.Spec.HostGrowthSelection
import Exec.Spec.Typing.ConfigTyping

/-! Every generated Wasm step has an admissible indexed witness. Strengthened
host steps additionally use the typed input store, available from Config_ok.
These are one-step source coverage results, not interpreter matching. -/

namespace Exec.Spec
open SpecExt

private theorem word32_bound (bits : Nat) (typed : wf_uN 32 (.mk_uN bits)) : bits < 2^32 := by
  cases typed
  norm_num at *
  omega

private theorem i32_bound (bits : Nat) (typed : wf_admininstr (Segment.i32 bits)) : bits < 2^32 := by
  cases typed
  cases_type wf_num_
  cases_type wf_uN
  norm_num [size,valtype_Inn] at *
  omega

private theorem table_index_bound (index : Nat) (typed : wf_admininstr (.TABLE_GROW (.mk_uN index))) : index < 2^32 := by
  cases typed
  apply word32_bound
  assumption

private theorem memory_update_view {before after : state} {next : meminst}
    (source : fun_with_meminst before (.mk_uN 0) next after) :
    ∃ s f, before = .mk_state s f ∧ 0 < f.MODULE.MEMS.length ∧
      after = .mk_state {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)} f := by
  cases source
  exact ⟨_,_,rfl,by assumption,rfl⟩

private theorem table_update_view {before after : state} {index : Nat} {next : tableinst}
    (source : fun_with_tableinst before (.mk_uN index) next after) :
    ∃ s f, before = .mk_state s f ∧ index < f.MODULE.TABLES.length ∧
      after = .mk_state {s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)} f := by
  cases source
  exact ⟨_,_,rfl,by assumption,rfl⟩

private theorem memory_success_choice (occurrence : Nat) (s : store) (f : frame) (delta : Nat) (next : meminst)
    (grown : fun_growmemory (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta (some next))
    (storeWf : wf_store s) (frameWf : wf_frame f) (deltaBound : delta < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length/65536 < 2^32) :
    ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
        ⟨⟨{s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)},f⟩,
          [Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length/65536)]⟩ := by
  obtain ⟨policy,admissible,selected⟩ := memory_reply_selectable occurrence _ delta (some next)
    (by intro after same; cases same; exact grown)
  let choices : SourceChoices := {defaultSourceChoices with memory := policy}
  have valid : choices.Admissible :=
    ⟨defaultSourceChoices_admissible.host,defaultSourceChoices_admissible.numeric,
      defaultSourceChoices_admissible.vector,admissible,defaultSourceChoices_admissible.table⟩
  have chosen : ChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      (memoryGrowthOutput s f (policy occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta)) :=
    .memory s f delta storeWf frameWf deltaBound (fun _ => mapped) (fun _ => bounded)
  rw [selected] at chosen
  exact ⟨choices,valid,chosen⟩

private theorem table_success_choice (occurrence : Nat) (s : store) (f : frame) (index delta : Nat)
    (value : ref) (next : tableinst)
    (grown : fun_growtable (fun_table ⟨s,f⟩ (.mk_uN index)) delta value (some next))
    (storeWf : wf_store s) (frameWf : wf_frame f) (indexBound : index < 2^32) (deltaBound : delta < 2^32)
    (mapped : index < f.MODULE.TABLES.length) (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
    ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices occurrence ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
        ⟨⟨{s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)},f⟩,
          [Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩ := by
  obtain ⟨policy,admissible,selected⟩ := table_reply_selectable occurrence _ delta value (some next)
    (by intro after same; cases same; exact grown)
  let choices : SourceChoices := {defaultSourceChoices with table := policy}
  have valid : choices.Admissible :=
    ⟨defaultSourceChoices_admissible.host,defaultSourceChoices_admissible.numeric,
      defaultSourceChoices_admissible.vector,defaultSourceChoices_admissible.memory,admissible⟩
  have chosen : ChoiceStep choices occurrence ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      (tableGrowthOutput s f index (policy occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value)) :=
    .table s f index delta value storeWf frameWf indexBound deltaBound (fun _ => mapped) (fun _ => bounded)
  rw [selected] at chosen
  exact ⟨choices,valid,chosen⟩

set_option maxHeartbeats 1600000 in
theorem step_choices {before after : config} (source : Step before after) (occurrence : Nat) :
    ∃ choices : SourceChoices, choices.Admissible ∧ ChoiceStep choices occurrence before [] after := by
  induction source
  case pure z body result source input output => exact pure_step_choices source occurrence z input output
  case read z body result source input output =>
    exact ⟨defaultSourceChoices,defaultSourceChoices_admissible,.ordinary_read source input output⟩
  case ctxt_label z arity continuation body z' result source input output inner outer ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih
    exact ⟨choices,admissible,.label chosen input output⟩
  case ctxt_frame s ambient arity inner body s' inner' result source input output inside outside ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih
    exact ⟨choices,admissible,.frame chosen input output⟩
  case ctxt_instrs z front body tail z' result source nonempty input output inside outside ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih
    exact ⟨choices,admissible,.instrs chosen nonempty input output⟩
  case memory_grow_succeed =>
    rename_i z delta next option afterState relation update present selected input output zeroWf
    cases option with
    | none => contradiction
    | some result =>
      simp only [Option.get!_some] at selected
      subst next
      obtain ⟨s,f,rfl,mapped,rfl⟩ := memory_update_view update
      have parts := wf_state_parts (wf_config_parts input).1
      have deltaBound := i32_bound delta ((wf_config_parts input).2 _ (by simp [Segment.i32]))
      have bounded := i32_bound (rat_to_nat (((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length : Rat)/(64*Ki : Rat)))
        ((wf_config_parts output).2 _ (by simp [Segment.i32]))
      simp only [memory_pages_nat] at bounded
      simpa only [memory_pages_nat,Segment.i32] using
        memory_success_choice occurrence s f delta result relation parts.1 parts.2 deltaBound mapped bounded
  case table_grow_succeed =>
    rename_i z value delta index next option afterState relation update present selected input output
    cases index with | mk_uN index =>
    cases option with
    | none => contradiction
    | some result =>
      simp only [Option.get!_some] at selected
      subst next
      obtain ⟨s,f,rfl,mapped,rfl⟩ := table_update_view update
      have parts := wf_state_parts (wf_config_parts input).1
      have deltaBound := i32_bound delta ((wf_config_parts input).2 _ (by simp [Segment.i32]))
      have indexBound := table_index_bound index ((wf_config_parts input).2 _ (by simp))
      have bounded := i32_bound (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length
        ((wf_config_parts output).2 _ (by simp [Segment.i32]))
      exact table_success_choice occurrence s f index delta value result relation parts.1 parts.2 indexBound deltaBound mapped bounded
  case memory_grow_fail =>
    rename_i z delta result integer input output
    have same : result = 2^32-1 := inv_signed_deterministic integer
      (by simpa using fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
    subst result
    cases z with | mk_state s f =>
    have parts := wf_state_parts (wf_config_parts input).1
    have deltaBound := i32_bound delta ((wf_config_parts input).2 _ (by simp [Segment.i32]))
    refine ⟨defaultSourceChoices,defaultSourceChoices_admissible,.memory s f delta parts.1 parts.2 deltaBound ?_ ?_⟩
    all_goals simp [defaultSourceChoices]
  case table_grow_fail =>
    rename_i z value delta index result integer input output
    have same : result = 2^32-1 := inv_signed_deterministic integer
      (by simpa using fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
    subst result
    cases z with | mk_state s f =>
    cases index with | mk_uN index =>
    have parts := wf_state_parts (wf_config_parts input).1
    have deltaBound := i32_bound delta ((wf_config_parts input).2 _ (by simp [Segment.i32]))
    have indexBound := table_index_bound index ((wf_config_parts input).2 _ (by simp))
    refine ⟨defaultSourceChoices,defaultSourceChoices_admissible,
      .table s f index delta value parts.1 parts.2 indexBound deltaBound ?_ ?_⟩
    all_goals simp [defaultSourceChoices]
  all_goals
    refine ⟨defaultSourceChoices,defaultSourceChoices_admissible,.ordinary_write ?_ ?_⟩
    swap
    constructor
    solve_by_elim (maxDepth := 16) [Step.local_set,Step.global_set,Step.table_set_trap,Step.table_set_val,
       Step.elem_drop,Step.store_num_trap,Step.store_num_val,Step.store_pack_trap,Step.store_pack_val,
       Step.vstore_oob,Step.vstore_val,Step.vstore_lane_oob,Step.vstore_lane_val,Step.data_drop]

def configurationStore : config → store
  | .mk_config (.mk_state s _) _ => s

private theorem selectable_host_step (occurrence : Nat) (request : HostRequest) (reply : HostReply)
    (f : frame) (typed : Store_ok request.before) (frameWf : wf_frame f)
    (host : HostFunction request.before request.address request.identity request.params request.results)
    (arguments : ResultsTyped request.before request.params request.args)
    (permitted : reply.Admissible request.before request.results) :
    ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices occurrence ⟨⟨request.before,f⟩,vals request.args ++ [.CALL_ADDR request.address]⟩
        [.call request.address request.args reply.result] (reply.configuration f) := by
  obtain ⟨policy,admissible,selected⟩ := host_reply_selectable occurrence request reply permitted
  let choices : SourceChoices := {defaultSourceChoices with host := policy}
  have valid : choices.Admissible :=
    ⟨admissible,defaultSourceChoices_admissible.numeric,defaultSourceChoices_admissible.vector,
      defaultSourceChoices_admissible.memory,defaultSourceChoices_admissible.table⟩
  have chosen := ChoiceStep.host (choices := choices) (occurrence := occurrence)
    request.before f request.address request.identity request.params request.results request.args typed frameWf host arguments
  change ChoiceStep choices occurrence ⟨⟨request.before,f⟩,vals request.args ++ [.CALL_ADDR request.address]⟩
    [.call request.address request.args (policy occurrence request.before request.address request.identity request.params request.results request.args).result]
    ((policy occurrence request.before request.address request.identity request.params request.results request.args).configuration f) at chosen
  rw [selected] at chosen
  exact ⟨choices,valid,chosen⟩

/-- All strengthened source steps from typed stores are represented, including
host effects and contexts. No interpreter execution is assumed. -/
theorem host_step_choices {before events after} (source : StepH before events after)
    (typed : Store_ok (configurationStore before)) (occurrence : Nat) :
    ∃ choices : SourceChoices, choices.Admissible ∧ ChoiceStep choices occurrence before events after := by
  induction source with
  | step source => exact step_choices source occurrence
  | @host_return s next f address identity params results args values host arguments extension afterTyped valueTyped input output =>
    have frameWf := (wf_state_parts (wf_config_parts input).1).2
    have allowed : (HostReply.mk next (some values)).Admissible s results :=
      ⟨extension,afterTyped,by intro returned same; cases same; exact valueTyped⟩
    exact selectable_host_step occurrence ⟨s,address,identity,params,results,args⟩ ⟨next,some values⟩
      f typed frameWf host arguments allowed
  | @host_trap s next f address identity params results args host arguments extension afterTyped input output =>
    have frameWf := (wf_state_parts (wf_config_parts input).1).2
    have allowed : (HostReply.mk next none).Admissible s results :=
      ⟨extension,afterTyped,by intro returned impossible; cases impossible⟩
    exact selectable_host_step occurrence ⟨s,address,identity,params,results,args⟩ ⟨next,none⟩
      f typed frameWf host arguments allowed
  | ctxt_label source input output inside outside ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih typed
    exact ⟨choices,admissible,.label chosen input output⟩
  | ctxt_frame source input output inside outside ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih typed
    exact ⟨choices,admissible,.frame chosen input output⟩
  | ctxt_instrs source nonempty input output inside outside ih =>
    obtain ⟨choices,admissible,chosen⟩ := ih typed
    exact ⟨choices,admissible,.instrs chosen nonempty input output⟩

theorem typed_step_choices {before events after types} (source : StepH before events after)
    (typed : Config_ok before types) (occurrence : Nat) :
    ∃ choices : SourceChoices, choices.Admissible ∧ ChoiceStep choices occurrence before events after := by
  apply host_step_choices source _ occurrence
  cases before with | mk_config z body =>
  cases z with | mk_state s f =>
  exact config_ok_store typed

end Exec.Spec

