import Exec.Abs.Sim.OpenContext
namespace Exec.Abs.OpenContext
open SpecExt Exec.Spec Exec.Spec.OpenHost

/-- Resuming the saved host context with values gives precisely the flat
abstract caller continuation, including its retained operand prefix and labels. -/
theorem host_values_complete (ambient : frame) (ha : wf_frame ambient) (f : AFrame)
    (rest : List AFrame) (hr : Forall FrameWf rest) (after : List instr) (hc : Forall wf_instr after)
    (front : List val) (hv : Forall wf_val front) (hl : LabelsWf f.labels)
    (heights : ∀label∈f.labels,label.height≤front.length) (fresh : store) (returned : List val) :
    (host ambient ha f rest hr after hc front hv hl).plug ⟨⟨fresh,f.toFrame⟩,vals returned⟩=
      decode ⟨fresh,ambient,{f with vals:=front++returned,code:=after}::rest,[]⟩ := by
  rw [host_plug]
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  rfl

/-- Direct host capture retains a concrete equality for every returned value
list, rather than merely two existential source executions with the same event. -/
theorem host_call_pending_completion (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (index address : Nat) (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code:=.CALL (.mk_uN index)::after}::rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code:=.CALL (.mk_uN index)::after}::rest,[]⟩=.host address args results resume)
    (expected : resulttype)
    (configurationTyped : Config_ok (decode ⟨s,ambient,{f with code:=.CALL (.mk_uN index)::after}::rest,[]⟩) expected) :
    ∃pending : Pending,pending.before=s ∧ pending.address=address ∧ pending.arguments=args ∧ pending.results=results ∧
      StepH (decode ⟨s,ambient,{f with code:=.CALL (.mk_uN index)::after}::rest,[]⟩) [] pending.initial ∧
      Config_ok pending.initial expected ∧
      ∀fresh returned,pending.completed ⟨fresh,some returned⟩=decode (finishHost resume fresh returned) := by
  obtain ⟨suspended,identity,params,hostFunction,argumentsTyped⟩ := host_call_preparation s ambient f rest after index address args results resume typed step
  obtain ⟨front,split,resumeEq,resolve,bounded,frameWf,labelsWf,frontWf,afterWf,restWf,heights⟩ := host_call_site s ambient f rest after index address args results resume typed step
  let context := host ambient typed.ambient f rest restWf after afterWf front frontWf labelsWf
  let pending : Pending := ⟨s,f.toFrame,context,address,identity,params,results,args,hostFunction,argumentsTyped,frameWf⟩
  have first := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs (call_resolve s f.toFrame index address typed.store frameWf resolve bounded)
      args (after.map admininstr_instr) (resultsTyped_wf argumentsTyped) (wf_instrs afterWf))
      f.labels front labelsWf frontWf) typed.ambient restWf
  have prepared : StepH (decode ⟨s,ambient,{f with code:=.CALL (.mk_uN index)::after}::rest,[]⟩) [] pending.initial := by
    simp only [Pending.initial,pending,context,host_plug]
    simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
    rw [split,decodeLabels_move_values _ _ _ _ heights]
    simpa [instrContext,vals,List.append_assoc,AFrame.toFrame,AFrame.arity,admininstr_instr] using first
  refine ⟨pending,rfl,rfl,rfl,rfl,prepared,stepH_config_preserved prepared configurationTyped,?_⟩
  intro fresh returned
  simp only [Pending.completed,pending,context,HostReply.configuration]
  rw [host_values_complete _ _ _ _ _ _ _ _ _ _ heights,resumeEq]
  rfl
theorem indirect_host_pending_completion (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (address : Nat) (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (step : Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
      f rest table type after=.host address args results resume)
    (expected : resulttype)
    (configurationTyped : Config_ok (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) expected) :
    ∃pending : Pending,pending.before=s ∧ pending.address=address ∧ pending.arguments=args ∧ pending.results=results ∧
      StepH (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] pending.initial ∧
      Config_ok pending.initial expected ∧
      ∀fresh returned,pending.completed ⟨fresh,some returned⟩=decode (finishHost resume fresh returned) := by
  obtain ⟨suspended,identity,params,front,position,hostFunction,argumentsTyped,split,resumeEq,resolve,
    tableBound,typeBound,positionBound,frameWf,labelsWf,frontWf,afterWf,restWf,heights⟩ :=
    Indirect.host_preparation s ambient f rest table type after address args results resume typed step
  let context := host ambient typed.ambient f rest restWf after afterWf front frontWf labelsWf
  let pending : Pending := ⟨s,f.toFrame,context,address,identity,params,results,args,hostFunction,argumentsTyped,frameWf⟩
  have first := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs (call_indirect_resolve s f.toFrame table type position address typed.store frameWf tableBound typeBound positionBound resolve)
      args (after.map admininstr_instr) (resultsTyped_wf argumentsTyped) (wf_instrs afterWf))
      f.labels front labelsWf frontWf) typed.ambient restWf
  have prepared : StepH (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] pending.initial := by
    simp only [Pending.initial,pending,context,host_plug]
    simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
    rw [split,List.append_assoc,decodeLabels_move_values _ _ _ _ heights]
    simpa [instrContext,vals,List.append_assoc,AFrame.toFrame,AFrame.arity,admininstr_instr,integerVal,Segment.i32,numtype_Inn,admininstr_val] using first
  refine ⟨pending,rfl,rfl,rfl,rfl,prepared,stepH_config_preserved prepared configurationTyped,?_⟩
  intro fresh returned
  simp only [Pending.completed,pending,context,HostReply.configuration]
  rw [host_values_complete _ _ _ _ _ _ _ _ _ _ heights,resumeEq]
  rfl

end Exec.Abs.OpenContext
