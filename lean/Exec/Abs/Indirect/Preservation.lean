import Exec.Abs.Indirect.Progress
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
