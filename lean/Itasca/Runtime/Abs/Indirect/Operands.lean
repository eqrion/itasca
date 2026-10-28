import Itasca.Runtime.Abs.Stateful.TableTyping
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

theorem operands {s : store} {f : AFrame} {table type : Nat} {after : List instr}
    (typed : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} []) :
    ∃ C front args params results position,
      ModuleBindings s f.module C ∧
      (∃limits,C.TABLES[table]?=some (.mk_tabletype limits .FUNCREF)) ∧
      C.TYPES[type]?=some ⟨.mk_list params,.mk_list results⟩ ∧
      f.vals=front++args++[integerVal .I32 position] ∧ position<2^32 ∧
      ResultsTyped s params args ∧ Forall wf_val front ∧
      (∀label∈f.labels,label.height≤front.length) ∧
      FrameTyped s {f with code:=after,vals:=front} results ∧ table<2^32 ∧ type<2^32 := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨prefixTypes,inputs,outputs,operation,stack,continuation,heights⟩ := codeStack_after_bounds (value_types_concrete f.vals) hc
    cases operation with
    | call_indirect _ _ _ params results limits tableBound tableType typeBound signature contextWf instructionWf _ =>
      simp only [labelContext,proj_uN_0] at tableBound tableType typeBound signature
      have all : ResultsTyped s (prefixTypes++(params++[valtype.I32])) f.vals := by rw [←stack];exact values
      obtain ⟨front,operands,split,frontTyped,operandTyped⟩ := resultsTyped_split all
      obtain ⟨args,index,operandSplit,argsTyped,indexTyped⟩ := resultsTyped_split operandTyped
      cases indexTyped with
      | cons selected nil =>
        cases nil
        obtain ⟨position,rfl,bounded⟩ := integer_val_inv (ty:=.I32) selected
        have selectedTable : C.TABLES[table]?=some (.mk_tabletype limits .FUNCREF) := by
          rw [List.getElem?_eq_getElem tableBound]
          exact congrArg some (by simpa only [getElem!_pos C.TABLES table tableBound] using tableType)
        have selectedType : C.TYPES[type]?=some ⟨.mk_list params,.mk_list outputs⟩ := by
          rw [List.getElem?_eq_getElem typeBound]
          exact congrArg some (by simpa only [getElem!_pos C.TYPES type typeBound] using signature)
        refine ⟨C,front,args,params,outputs,position,bindings,⟨limits,selectedTable⟩,selectedType,?_,bounded,argsTyped,
          resultsTyped_wf frontTyped,?_,?_,?_,?_⟩
        · simpa only [operandSplit,List.append_assoc] using split
        · intro label member
          rw [resultsTyped_length frontTyped]
          exact heights label member
        · have frontTypes := results_type_of_typed frontTyped
          apply FrameTyped.mk (f:={f with code:=after,vals:=front}) C bindings localTypes locals (by simpa only [frontTypes] using frontTyped) returns ?_ hw
          simpa only [frontTypes] using continuation
        · cases instructionWf;rename_i ht hy;cases ht;norm_num at *;omega
        · cases instructionWf;rename_i ht hy;cases hy;norm_num at *;omega
end Itasca.Runtime.Abs.Indirect
