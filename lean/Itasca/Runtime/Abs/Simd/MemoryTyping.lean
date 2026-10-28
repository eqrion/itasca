import Itasca.Runtime.Abs.Simd.Source
import Itasca.Runtime.Abs.Simd.Transition
import Itasca.Runtime.Abs.Core.MemoryTyping
import Itasca.Runtime.Abs.Core.MemoryMutation

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec

theorem MemorySignature.memory_present {source inputs outputs C signature}
    (shape : MemorySignature source inputs outputs) (typed : Instr_ok C source signature) :
    0 < C.MEMS.length := by cases shape <;> cases typed <;> assumption

theorem MemorySignature.typed_operands {source inputs outputs}
    (signature : MemorySignature source inputs outputs) {s : _root_.store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s {f with code := source :: after} []) :
    ∃ front operands address object, f.vals = front ++ operands ∧ ResultsTyped s inputs operands ∧
      f.module.MEMS[0]? = some address ∧ s.MEMS[address]? = some object ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,values,operandTypes,valid,heights⟩ :=
    frame_typed_operands_bounds typed
  have present : 0 < C.MEMS.length := by
    simpa only [labelContext] using signature.memory_present operation
  obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
  have principal := signature.principal operation
  simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
  rcases principal with ⟨rfl,rfl⟩
  exact ⟨front,operands,address,object,values,operandTypes,mapped,found,valid,heights⟩

theorem MemorySignature.results_typed {source inputs outputs}
    (signature : MemorySignature source inputs outputs) {s : _root_.store} {values : List val}
    (storeWf : wf_store s) (valid : Forall wf_val values) (types : values.map valueType = outputs) :
    ResultsTyped s outputs values := by
  have vectorResults {values : List val} (valid : Forall wf_val values)
      (types : values.map valueType = [.V128]) : ResultsTyped s [.V128] values := by
    cases values with
    | nil => simp at types
    | cons value tail =>
      simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at types
      rcases types with ⟨typeEq,rfl⟩
      exact .cons (numeric_value_typed (Or.inl rfl) storeWf
        (valid value (by simp)) typeEq) .nil
  cases signature
  all_goals first
    | exact vectorResults valid types
    | have empty := List.map_eq_nil_iff.mp types; subst values; exact .nil

theorem MemorySignature.frame_preservation {source inputs outputs}
    (signature : MemorySignature source inputs outputs) {s : _root_.store} {f : AFrame} {after : List instr}
    (front operands results : List val) (types : operands.map valueType = inputs)
    (resultTyped : ResultsTyped s outputs results)
    (typed : FrameTyped s {f with code := source :: after, vals := front ++ operands} []) :
    FrameTyped s {f with code := after, vals := front ++ results} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      codeStack_after (value_types_concrete (front ++ operands)) code
    have principal := signature.principal instruction
    simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
    rcases principal with ⟨rfl,rfl⟩
    simp only [List.map_append,types,List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using resultsTyped_take front.length values
    have resultTypes := results_type_of_typed resultTyped
    apply FrameTyped.mk (f := {f with code := after, vals := front ++ results}) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa only [ResultsTyped,List.map_append,resultTypes] using List.rel_append frontTyped resultTyped
    · simpa only [List.map_append,List.append_nil,resultTypes,stack] using continuation

/-- Pure source description of the only SIMD store mutation: one memory byte
payload. The source reduction itself checks addressing and trap behavior. -/
inductive MemoryChange (before : _root_.store) (frame : frame) : _root_.store → Prop where
  | same : MemoryChange before frame before
  | write (start : Nat) (payload : List byte) (valid : Forall wf_byte payload) :
      MemoryChange before frame (Spec.memoryPayloadWrite before frame start payload)

theorem MemoryChange.functions {before frame after} (change : MemoryChange before frame after) :
    after.FUNCS = before.FUNCS := by cases change <;> rfl

theorem MemoryChange.typed {before frame after} (change : MemoryChange before frame after)
    (storeWf : wf_store before) (contents : StoreContentsTyped before)
    {address object} (mapped : frame.MODULE.MEMS[0]? = some address)
    (found : before.MEMS[address]? = some object) :
    Extend_store before after ∧ StoreContentsTyped after := by
  cases change with
  | same => exact ⟨extend_store_refl before storeWf,contents⟩
  | write start payload valid => exact
      ⟨memoryPayloadWrite_extends before frame address start object payload storeWf contents mapped found valid,
       contents.memory_write storeWf frame address start object payload mapped found valid⟩

end Itasca.Runtime.Abs.Simd
