import Itasca.Runtime.SourceMachine.Memory.Semantics
import Itasca.Runtime.SourceMachine.Core.GlobalTyping

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem extern_mem_lookup {s : store} {address : Nat} {ty : memtype}
    (typed : Externaddr_ok s (.MEM address) (.MEM ty)) :
    ∃ object, s.MEMS[address]? = some object := by
  generalize he : externaddr.MEM address = external at typed
  generalize ht : externtype.MEM ty = externalType at typed
  induction typed generalizing ty with
  | mem a object bound found wf ext =>
    cases he
    cases ht
    refine ⟨object,?_⟩
    simpa [getElem!_pos, bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | mem old new relation _ _ => exact ih he rfl
    | _ => cases ht
  | _ => cases he

theorem ModuleBindings.memory_lookup {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (present : 0 < C.MEMS.length) :
    ∃ address object, m.MEMS[0]? = some address ∧ s.MEMS[address]? = some object := by
  have left : 0 < m.MEMS.length := by rw [bindings.mems.length_eq]; exact present
  have relation := bindings.mems.get left present
  obtain ⟨object,lookup⟩ := extern_mem_lookup relation
  exact ⟨m.MEMS[0],object,List.getElem?_eq_getElem left,lookup⟩

theorem memory_load_typing {C : context} {ty : numtype} {packed : Option loadop_}
    (argument : memarg) {ins outs}
    (typed : Instr_ok C (.LOAD ty packed argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32] ∧ outs = [valtype_numtype ty] ∧ 0 < C.MEMS.length := by
  cases typed with
  | load_val => exact ⟨rfl,rfl,by assumption⟩
  | load_pack _ ty => cases ty <;> exact ⟨rfl,rfl,by assumption⟩

theorem memory_store_typing {C : context} {ty : numtype} {packed : Option sz}
    (argument : memarg) {ins outs}
    (typed : Instr_ok C (.STORE ty packed argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32,valtype_numtype ty] ∧ outs = [] ∧ 0 < C.MEMS.length := by
  cases typed with
  | store_val => exact ⟨rfl,rfl,by assumption⟩
  | store_pack _ ty => cases ty <;> exact ⟨rfl,rfl,by assumption⟩

theorem Memory.Load.typing {C : context} (op : Memory.Load) (argument : memarg) {ins outs}
    (typed : Instr_ok C (op.source argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32] ∧ outs = [valtype_numtype op.type] ∧ 0 < C.MEMS.length :=
  memory_load_typing argument typed

theorem Memory.Store.typing {C : context} (op : Memory.Store) (argument : memarg) {ins outs}
    (typed : Instr_ok C (op.source argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32,valtype_numtype op.type] ∧ outs = [] ∧ 0 < C.MEMS.length :=
  memory_store_typing argument typed

theorem memory_load_frame_continuation {s : store} {f : AFrame} {code : List instr}
    (op : Memory.Load) (argument : memarg) {front : List val} {address value : val}
    (h : FrameTyped s {f with code := op.source argument :: code, vals := front ++ [address]} [])
    (result : Val_ok s value (valtype_numtype op.type)) :
    ∃ memoryAddress object, f.module.MEMS[0]? = some memoryAddress ∧
      s.MEMS[memoryAddress]? = some object ∧
      FrameTyped s {f with code := code, vals := front ++ [value]} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [address])) hc
    obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
    obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
    simp only [List.map_append,List.map_cons,List.map_nil] at stack
    have length : (front.map valueType).length = base.length := by
      have lengths := congrArg List.length stack
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨baseEq,lastEq⟩ := List.append_inj stack length
    have prefixTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    have actualType := value_type_of_typed result
    refine ⟨memoryAddress,object,mapped,found,?_⟩
    apply FrameTyped.mk (f := {f with code := code, vals := front ++ [value]}) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,actualType] using
        List.rel_append prefixTyped (List.Forall₂.cons result List.Forall₂.nil)
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,actualType,baseEq] using continuation

theorem memory_store_frame_continuation {s : store} {f : AFrame} {code : List instr}
    (op : Memory.Store) (argument : memarg) {front : List val} {address value : val}
    (h : FrameTyped s {f with code := op.source argument :: code, vals := front ++ [address,value]} []) :
    ∃ memoryAddress object, f.module.MEMS[0]? = some memoryAddress ∧
      s.MEMS[memoryAddress]? = some object ∧
      FrameTyped s {f with code := code, vals := front} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [address,value])) hc
    obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
    obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
    simp only [List.map_append,List.map_cons,List.map_nil] at stack
    have length : (front.map valueType).length = base.length := by
      have lengths := congrArg List.length stack
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨baseEq,lastEq⟩ := List.append_inj stack length
    have prefixTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    refine ⟨memoryAddress,object,mapped,found,?_⟩
    apply FrameTyped.mk (f := {f with code := code, vals := front}) C
      bindings localTypes locals prefixTyped returns ?_ hw
    simpa only [List.append_nil,baseEq] using continuation

end Itasca.Runtime.SourceMachine
