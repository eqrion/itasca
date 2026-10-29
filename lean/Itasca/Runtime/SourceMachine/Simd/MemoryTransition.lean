import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.SourceMachine.Simd.Transition
import Itasca.Runtime.SourceMachine.Core.MemoryTyping
import Itasca.Runtime.SourceMachine.Core.MemoryMutation
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
SIMD memory transition typing and source simulation. Pure SIMD transition and shared memory mutation contracts remain separate.
-/

/-! ## Memory Typing -/

section

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

end

/-! ## Memory Transition -/

section

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec

/-- The source SIMD memory relation uses the generated local reduction and an
exact payload update. No frame typing or preservation conclusion is assumed. -/
inductive MemoryTransition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (source : instr) (inputs outputs : List valtype) : AResult → Prop where
  | next (front operands results : List val) (store : _root_.store)
      (values : f.vals = front ++ operands) (types : operands.map valueType = inputs)
      (resultTypes : results.map valueType = outputs)
      (change : MemoryChange s.store f.toFrame store)
      (effect : StepH ⟨⟨s.store,f.toFrame⟩,vals operands ++ [admininstr_instr source]⟩ []
        ⟨⟨store,f.toFrame⟩,vals results⟩) :
      MemoryTransition s f rest after source inputs outputs
        (.next ⟨store,s.ambient,{f with code := after, vals := front ++ results} :: rest,[]⟩)
  | trap (front operands : List val)
      (values : f.vals = front ++ operands) (types : operands.map valueType = inputs)
      (effect : StepH ⟨⟨s.store,f.toFrame⟩,vals operands ++ [admininstr_instr source]⟩ []
        ⟨⟨s.store,f.toFrame⟩,[.TRAP]⟩) :
      MemoryTransition s f rest after source inputs outputs .trap

theorem memory_transition_preservation {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs} {next : AState}
    (signature : MemorySignature source inputs outputs)
    (typed : CoreTyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs (.next next)) :
    CoreTyped next ∧ Extend_store s next.store := by
  cases step with
  | next front operands results store values types resultTypes change effect =>
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨_,_,address,object,_,_,mapped,found,_,_⟩ := signature.typed_operands hf
    obtain ⟨extension,contents⟩ := change.typed typed.typed.store typed.contents mapped found
    have resultWf : Forall wf_val results := by
      have wf := (wf_config_parts (stepH_wf effect).2).2
      intro value member
      exact val_wf_of_admin (wf _ (List.mem_map.mpr ⟨value,member,rfl⟩))
    have resultTyped := signature.results_typed (extend_store_wf extension).2 resultWf resultTypes
    have frameNext := signature.frame_preservation front operands results types resultTyped
      (by change f.vals = front ++ operands at values; simpa only [values] using hf.extend extension)
    have whole := typed.typed.extend_same extension change.functions
    exact ⟨⟨active_frame_preservation whole frameNext rfl,contents⟩,extension⟩

theorem MemorySignature.prefix_bounds {source inputs outputs}
    (signature : MemorySignature source inputs outputs) {s : _root_.store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s {f with code := source :: after} [])
    {front operands : List val} (values : f.vals = front ++ operands)
    (types : operands.map valueType = inputs) :
    Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨other,actual,_,_,split,actualTyped,_,_,_,heights⟩ := signature.typed_operands typed
  have equal : other.length = front.length := by
    have first := congrArg List.length split
    have second := congrArg List.length values
    have size := congrArg List.length types
    have actualSize := resultsTyped_length actualTyped
    simp only [List.length_append,List.length_map] at first second size
    omega
  have valid := (frameTyped_wf typed).2.2.1
  change Forall wf_val f.vals at valid
  rw [values] at valid
  exact ⟨fun v hv => valid v (List.mem_append_left _ hv),by simpa only [equal] using heights⟩

theorem memory_transition_simulation {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs} {next : AState}
    (signature : MemorySignature source inputs outputs)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs (.next next)) :
    NextSim ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩ next := by
  cases step with
  | next front operands results store values types resultTypes change effect =>
    change f.vals = front ++ operands at values
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨_,labelsWf,_,codeWf⟩ := frameTyped_wf hf
    obtain ⟨frontWf,heights⟩ := signature.prefix_bounds hf values types
    apply NextSim.single
    have simulated := mutable_stack_simulation s store ambient f rest source after front operands results
      typed.ambient labelsWf frontWf (fun op member => codeWf op (by simp [member])) hr heights effect
    simpa only [values] using simulated

theorem memory_transition_trap_simulation {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs}
    (signature : MemorySignature source inputs outputs)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩) [] ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  cases step with
  | trap front operands values types effect =>
    change f.vals = front ++ operands at values
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frameTyped_wf hf
    obtain ⟨frontWf,heights⟩ := signature.prefix_bounds hf values types
    have simulated := operand_trap_simulation s ambient f rest source after front operands
      typed.store typed.ambient frameWf labelsWf frontWf
      (fun op member => codeWf op (by simp [member])) hr heights effect
    simpa only [values] using simulated

end Itasca.Runtime.Abs.Simd

end
