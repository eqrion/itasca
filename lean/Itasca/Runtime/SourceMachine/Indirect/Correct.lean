import Itasca.Runtime.SourceMachine.Indirect.Definition
import Itasca.Runtime.SourceMachine.Indirect.Operands
import Itasca.Runtime.Spec.IndirectCallSource
import Itasca.Runtime.SourceMachine.Sim.Call
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
Indirect-call source progress, preservation and simulation, used by selected-call machine execution. Lookup contracts and host-call simulation remain separate.
-/

/-! ## Progress -/

section

namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

theorem type_selected {s : store} {f : AFrame} {C : context} {type : Nat} {signature : functype}
    (bindings : ModuleBindings s f.module C) (selected : C.TYPES[type]?=some signature) :
    fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=signature := by
  simp only [fun_type,AFrame.toFrame,proj_uN_0,←bindings.types,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]

end Itasca.Runtime.Abs.Indirect

end

/-! ## Preservation -/

section

namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

theorem invoke_preservation (s : store) (ambient : frame) (originalCode : List instr) (f : AFrame) (rest : List AFrame)
    (address : Nat) (after : List instr) (fn : funcinst) (params results : List valtype) (front args : List val)
    (typed : CoreTyped ⟨s,ambient,{f with code:=originalCode}::rest,[]⟩)
    (lookup : s.FUNCS[address]?=some fn) (signature : fn.TYPE=⟨.mk_list params,.mk_list results⟩)
    (arguments : ResultsTyped s params args) (caller : FrameTyped s {f with code:=after,vals:=front} results)
    (heights : ∀label∈f.labels,label.height≤front.length)
    (next : AState)
    (stepped : invoke ⟨s,ambient,{f with code:=originalCode}::rest,[]⟩ {f with vals:=front++args} rest address after=.next next) :
    CoreTyped next := by
  have types := results_type_of_typed arguments
  have lengthEq := resultsTyped_length arguments
  cases body : fn.CODE with
  | HOST host => simp [invoke,lookup,signature,←lengthEq,types,body] at stepped
  | FUNC index locals source =>
    obtain ⟨defaults,initial⟩ := function_defaults typed.typed.functions (List.mem_of_getElem? lookup) body
    have functionTyped := typed.typed.functions fn (List.mem_of_getElem? lookup)
    simp only [body] at functionTyped
    obtain ⟨C,bindings,emptyLocals,emptyLabels,returns,functionTyped⟩ := functionTyped
    rw [signature] at functionTyped
    obtain ⟨actualDefaults,actualInitial,callee⟩ := callee_frame_typed typed.typed.store
      (function_module_wf typed.typed.store (List.mem_of_getElem? lookup)) bindings emptyLocals emptyLabels functionTyped arguments address
    have same := Option.some.inj (initial.symm.trans actualInitial)
    subst actualDefaults
    have nextEq : next=⟨s,ambient,
        ⟨address,results,args++defaults,fn.MODULE,[⟨results,results,[],0,[]⟩],source,[]⟩::
        {f with vals:=front,code:=after}::rest,[]⟩ := by
      simpa [invoke,lookup,signature,←lengthEq,types,body,initial] using stepped.symm
    rw [nextEq]
    refine ⟨?_,typed.contents⟩
    have tail : FramesTyped s rest f.resultTypes := by
      cases typed.typed.frames with | cons _ tail => exact tail
    refine ⟨typed.typed.store,typed.typed.functions,typed.typed.ambient,.cons callee (.cons caller tail),by simp [Forall],by simp,?_⟩
    intro frame member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact frameTyped_heights callee
    · exact heights
    · exact typed.typed.heights frame (by simp [member])

theorem preservation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    CoreTyped next := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none =>
    simp only [step,values,pop_append,decoded,resolved] at stepped
    cases stepped
  | some address =>
    obtain ⟨reference,fn,lookup,signature⟩ := (resolve_iff s f table type position address).mp resolved
    have actualType : fn.TYPE=⟨.mk_list params,.mk_list results⟩ := signature.symm.trans (type_selected bindings typeSelected)
    apply invoke_preservation s ambient _ f rest address after fn params results front args typed lookup actualType arguments caller heights next
    simpa only [step,values,pop_append,decoded,resolved] using stepped
end Itasca.Runtime.Abs.Indirect

end

/-! ## Simulation -/

section

namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec
theorem indirect_call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (table type position address : Nat) (typeIndex : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (baseValues args defaults : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : IndirectTarget s f.toFrame table type position address)
    (tableBound : table<2^32) (typeBound : type<2^32) (positionBound : position<2^32)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepsHN 2
      (decode ⟨s, ambient, { f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after, vals := baseValues ++ args ++ [integerVal .I32 position] } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have h₁ := stepH_instrs (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
    args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := stepH_instrs (call_invoke s f.toFrame address typeIndex moduleInst
    params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := stepH_active ambient rest f.arity
    (stepH_decodeLabels h₁ f.labels baseValues hl hv) ha hr
  have h₄ := stepH_active ambient rest f.arity
    (stepH_decodeLabels h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := StepsHN.cons h₃ (StepsHN.cons h₄ (StepsHN.refl (stepH_wf h₄).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [List.append_assoc]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr, integerVal, Segment.i32, numtype_Inn, admininstr_val] using both

end Itasca.Runtime.Abs.Indirect

end

/-! ## Correct -/

section

namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

theorem next_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    StepsHN 2 (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
  have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
  have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none => simp only [step,values,pop_append,decoded,resolved] at stepped;cases stepped
  | some address =>
    have target := (resolve_iff s f table type position address).mp resolved
    obtain ⟨reference,fn,lookup,signature⟩ := target
    have actualType : fn.TYPE=⟨.mk_list params,.mk_list results⟩ := signature.symm.trans (type_selected bindings typeSelected)
    have argTypes := results_type_of_typed arguments
    have argLength := resultsTyped_length arguments
    cases body : fn.CODE with
    | HOST host => simp [step,values,←List.append_assoc,pop_append,decoded,resolved,invoke,lookup,actualType,←argLength,argTypes,body] at stepped
    | FUNC index locals source =>
      have functionTyped := typed.typed.functions fn (List.mem_of_getElem? lookup)
      simp only [body] at functionTyped
      obtain ⟨Cfn,fnBindings,noLocals,noLabels,noReturns,functionTyped⟩ := functionTyped
      rw [actualType] at functionTyped
      obtain ⟨types,localEq,nonbot⟩ := function_local_types functionTyped
      subst locals
      obtain ⟨defaults,initial,defaultsTyped⟩ := defaultLocals_typed typed.typed.store types nonbot
      have record : fn=⟨⟨.mk_list params,.mk_list results⟩,fn.MODULE,.FUNC index (types.map local.LOCAL) source⟩ := by
        cases fn
        simp_all
      have installed : next=⟨s,ambient,
        ⟨address,results,args++defaults,fn.MODULE,[⟨results,results,[],0,[]⟩],source,[]⟩::
        {f with vals:=front,code:=after}::rest,[]⟩ := by
        simp only [step,values,pop_append,decoded,resolved] at stepped
        simpa [invoke,lookup,actualType,←argLength,argTypes,body,initial] using stepped.symm
      have simulation := indirect_call_simulation s ambient f rest after table type position address index fn.MODULE params results types source front args defaults
        typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights ⟨reference,fn,lookup,signature⟩ tableBound typeBound bounded
        (record ▸ lookup) nonbot initial (resultsTyped_wf arguments) argLength
      simpa only [installed,values] using simulation

theorem invoke_not_trap (s : AState) (f : AFrame) (rest : List AFrame) (address : Nat) (after : List instr) :
    invoke s f rest address after ≠ .trap := by
  unfold invoke
  repeat' first | split | (dsimp only) | (intro impossible;cases impossible)

theorem trap_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.trap) :
    ∃count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
  have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
  have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | some address =>
    simp only [step,values,pop_append,decoded,resolved] at stepped
    exact (invoke_not_trap _ _ _ _ _ stepped).elim
  | none =>
    have missing : ¬∃address,IndirectTarget s f.toFrame table type position address := by
      rintro ⟨address,target⟩
      have same := (resolve_iff s f table type position address).mpr target
      rw [resolved] at same
      cases same
    have source := call_indirect_trap s f.toFrame table type position typed.typed.store frameWf tableBound typeBound bounded missing
    have allFront : Forall wf_val (front++args) := forall_append frontWf (resultsTyped_wf arguments)
    have allHeights : ∀label∈f.labels,label.height≤(front++args).length := by
      intro label member
      have bound := heights label member
      simp only [List.length_append]
      omega
    have full := operand_trap_simulation s ambient f rest (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) after
      (front++args) [integerVal .I32 position] typed.typed.store typed.typed.ambient frameWf labelsWf allFront tailWf restWf allHeights
      (by simpa only [vals,List.map_cons,List.map_nil,admininstr_val,integerVal,numtype_Inn,admininstr_instr,Segment.i32,List.singleton_append] using source)
    simpa only [values] using full
end Itasca.Runtime.Abs.Indirect

end
