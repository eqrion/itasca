import Exec.Abs.Indirect.Preservation
import Exec.Abs.Indirect.Simulation
import Exec.Abs.Core.Trap
namespace Exec.Abs.Indirect
open SpecExt Exec.Spec

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
end Exec.Abs.Indirect
