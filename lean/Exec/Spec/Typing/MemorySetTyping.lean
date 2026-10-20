import Exec.Spec.Typing.LocalGlobalWriteTyping
import Exec.Spec.Typing.MemoryWriteTyping
/-! Generated scalar/SIMD memory writes preserve source stores, frames, and stack typing. -/

namespace Exec.Spec
open SpecExt

theorem external_memory_lookup {s : store} {address : Nat} {type : externtype}
    (typed : Externaddr_ok s (.MEM address) type) : ∃ object, s.MEMS[address]?=some object := by
  generalize addressEq : externaddr.MEM address=external at typed
  induction typed with
  | mem a object bound found _ _ =>
    cases addressEq
    refine ⟨object,?_⟩
    simpa [getElem!_pos,bound] using congrArg some found
  | sub external old new typed sub _ _ _ ih => exact ih addressEq
  | _ => cases addressEq

theorem FrameEnvironment.memory_lookup {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : idx) (bound : proj_uN_0 index<context.MEMS.length) :
    ∃ address object, frame.MODULE.MEMS[proj_uN_0 index]?=some address ∧ s.MEMS[address]?=some object := by
  have paired := environment.memory_addresses
  have addressBound : proj_uN_0 index<frame.MODULE.MEMS.length := by rw [paired.length_eq]; exact bound
  have relation := paired.get addressBound bound
  simp only [List.get_eq_getElem] at relation
  obtain ⟨object,found⟩ := external_memory_lookup relation
  exact ⟨frame.MODULE.MEMS[proj_uN_0 index],object,List.getElem?_eq_getElem addressBound,found⟩

def MemoryWriteInstruction : admininstr → Bool
  | .STORE _ _ _ | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ => true
  | _ => false

theorem memory_write_context_bound {s : store} {context : _root_.context} {instruction : admininstr}
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (memory : MemoryWriteInstruction instruction=true) : 0<context.MEMS.length := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases primitive <;> simp [MemoryWriteInstruction,admininstr_instr] at memory
    all_goals assumption
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [MemoryWriteInstruction,admininstr_ref] at memory
  all_goals simp [MemoryWriteInstruction] at memory

theorem memory_payload_state_typed {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    (bound : proj_uN_0 index<context.MEMS.length) (position count : Nat) (payload : List byte)
    {after : state} (updated : fun_with_mem ⟨s,frame⟩ index position count payload after) :
    match after with
    | ⟨store,nextFrame⟩ => nextFrame=frame ∧ Extend_store s store ∧ Store_ok store := by
  obtain ⟨address,object,addressFound,found⟩ := environment.memory_lookup index bound
  have actualAddress : frame.MODULE.MEMS[proj_uN_0 index]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  cases updated
  have givenPost : wf_state ⟨{s with MEMS := s.MEMS.modify (frame.MODULE.MEMS[proj_uN_0 index]!) (fun object => {object with BYTES := splice object.BYTES payload position})},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨sourceMemoryUpdate s address position payload,frame⟩ := by
    simpa only [sourceMemoryUpdate,actualAddress,list_modify_as_set] using givenPost
  have effect := memory_update_store_typed storeTyped address (List.getElem?_eq_some_iff.mp found).1 position payload
    (wf_state_parts normalizedPost).1
  simp only [actualAddress,list_modify_as_set]
  exact ⟨True.intro,effect⟩

theorem memory_write_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) {args : List val} {op : admininstr}
    (memory : MemoryWriteInstruction op=true) (arity : args.length=2)
    (position count : Nat) (payload : List byte) {after : state}
    (updated : fun_with_mem ⟨s,frame⟩ (.mk_uN 0) position count payload after) {input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [] input output := by
  have signature : writeInstructionSignature op=some (args.length,[]) := by
    cases op <;> simp [MemoryWriteInstruction] at memory
    all_goals simp only [writeInstructionSignature,arity]
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed signature
  have bound := memory_write_context_bound primitive memory
  have effect := memory_payload_state_typed storeTyped environment (.mk_uN 0) bound position count payload updated
  have wf := instrs_ok2_wf typed
  cases after with
  | mk_state store nextFrame =>
    obtain ⟨same,extension,postTyped⟩ := effect
    cases same
    exact ⟨extension,postTyped,FrameEnvironment.extend extension environment,
      realize_write_result inputSub outputSub (instrs_identity (extend_store_wf extension).2 wf.2.1 [])⟩

end Exec.Spec
