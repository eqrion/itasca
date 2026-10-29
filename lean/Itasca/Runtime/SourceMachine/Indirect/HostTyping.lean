import Itasca.Runtime.SourceMachine.HostTyping
import Itasca.Runtime.SourceMachine.Indirect.Correct
namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

/-- A typed indirect host call retains the selected address, concrete argument
suffix, and typed continuation produced by the actual abstract transition. -/
theorem host_preparation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
      f rest table type after = .host address args results resume) :
    HostPending resume results ∧ ∃ identity params front position,
      HostFunction s address identity params results ∧ ResultsTyped s params args ∧
      f.vals = front ++ args ++ [integerVal .I32 position] ∧
      resume = ⟨s,ambient,{f with vals := front,code := after} :: rest,[]⟩ ∧
      IndirectTarget s f.toFrame table type position address ∧
      table < 2^32 ∧ type < 2^32 ∧ position < 2^32 ∧
      wf_frame f.toFrame ∧ LabelsWf f.labels ∧ Forall wf_val front ∧
      Forall wf_instr after ∧ Forall FrameWf rest ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  have frameTyped : FrameTyped s {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.frames with | cons head _ => exact head
  obtain ⟨C,front,actualArgs,params,actualResults,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
  have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
  have tailTyped : FramesTyped s rest f.resultTypes := by cases typed.frames with | cons _ tail => exact tail
  have restWf := frames_typed_wf tailTyped
  have decoded : integer numtype.I32 (integerVal .I32 position) = some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none => simp only [step,values,pop_append,decoded,resolved] at stepped; cases stepped
  | some actualAddress =>
    have target := (resolve_iff s f table type position actualAddress).mp resolved
    obtain ⟨reference,fn,lookup,signature⟩ := target
    have actualType : fn.TYPE = ⟨.mk_list params,.mk_list actualResults⟩ := signature.symm.trans (type_selected bindings typeSelected)
    have argTypes := results_type_of_typed arguments
    have argLength := results_typed_length arguments
    cases body : fn.CODE with
    | HOST identity =>
      have observed := stepped
      simp [step,values,←List.append_assoc,pop_append,decoded,resolved,invoke,lookup,actualType,←argLength,argTypes,body] at observed
      obtain ⟨rfl,rfl,rfl,rfl⟩ := observed
      refine ⟨⟨typed.store,typed.functions,typed.ambient,.cons caller tailTyped,by simp,rfl,?_⟩,
        identity,params,front,position,?_,arguments,values,rfl,⟨reference,fn,lookup,signature⟩,
        tableBound,typeBound,bounded,frameWf,labelsWf,frontWf,tailWf,restWf,heights⟩
      · intro frame member
        rcases List.mem_cons.mp member with rfl | member
        · exact heights
        · exact typed.heights frame (by simp [member])
      · refine ⟨fn.MODULE,?_⟩
        have record : fn = ⟨⟨.mk_list params,.mk_list actualResults⟩,fn.MODULE,.HOST identity⟩ := by
          cases fn with
          | MKfuncinst ft mm cd =>
            change ft = _ at actualType
            change cd = _ at body
            subst ft
            subst cd
            rfl
        rw [←record]
        exact lookup
    | FUNC index locals source =>
      cases defaults : defaultLocals locals <;>
        simp [step,values,←List.append_assoc,pop_append,decoded,resolved,invoke,lookup,actualType,←argLength,argTypes,body,defaults] at stepped
end Itasca.Runtime.SourceMachine.Indirect
