import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
Sections, each formerly its own module: Exclusion, Transition, MemoryTransition.
-/

/-! ## Exclusion -/

section

namespace Itasca.Runtime.SourceMachine

/-- Source constructor tag used only to separate scalar/reference/control
heads from SIMD heads in cumulative syntactic certificates. -/
def simdSourceTag : instr → Bool
  | .VCONST _ _ | .VVUNOP _ _ | .VVBINOP _ _ | .VVTERNOP _ _ | .VVTESTOP _ _
  | .VUNOP _ _ | .VBINOP _ _ | .VTESTOP _ _ | .VRELOP _ _ | .VSHIFTOP _ _
  | .VBITMASK _ | .VSWIZZLE _ | .VSHUFFLE _ _ | .VSPLAT _ | .VEXTRACT_LANE _ _ _
  | .VREPLACE_LANE _ _ | .VEXTUNOP _ _ _ | .VEXTBINOP _ _ _ | .VNARROW _ _ _
  | .VCVTOP _ _ _ | .VLOAD _ _ _ | .VLOAD_LANE _ _ _ _ | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ => true
  | _ => false

theorem SimdInstr.source_tag {source} (allowed : SimdInstr source) : simdSourceTag source = true := by
  cases allowed with
  | pure signature => cases signature <;> rfl
  | memory signature => cases signature <;> rfl
  | constant => rfl

theorem PureHead.simd_tag {source} (allowed : PureHead source) : simdSourceTag source = false := by
  cases allowed with
  | numeric op => cases op <;> rfl
  | _ => rfl

theorem CoreHead.simd_tag {source} (allowed : CoreHead source) : simdSourceTag source = false := by
  cases allowed with
  | pure old => exact old.simd_tag
  | load op arg => cases op <;> rfl
  | store op arg => cases op <;> rfl
  | _ => rfl

theorem ScalarHead.simd_tag {source} (allowed : ScalarHead source) : simdSourceTag source = false := by
  cases allowed with
  | core old => exact old.simd_tag
  | float op => cases op <;> rfl

end Itasca.Runtime.SourceMachine

end

/-! ## Transition -/

section

namespace Itasca.Runtime.SourceMachine.Simd
open SpecExt Itasca.Runtime.Spec

/-- A source pure reduction retains every permitted numerical result, including
all permitted floating-point NaN choices. -/
def PureResult (source : instr) (output : valtype) (operands : List val) (value : val) : Prop :=
  Step_pure (vals operands ++ [admininstr_instr source]) [admininstr_val value] ∧
  valueType value = output

theorem PureResult.wf {source output operands value}
    (effect : PureResult source output operands value) : wf_val value :=
  pure_singleton_wf effect.1

theorem PureSignature.frame_preservation {source inputs output}
    (signature : PureSignature source inputs output) {s : store} {f : AFrame} {after : List instr}
    (front operands : List val) (value : val) (types : operands.map valueType = inputs)
    (storeWf : wf_store s) (effect : PureResult source output operands value)
    (typed : FrameTyped s {f with code := source :: after, vals := front ++ operands} []) :
    FrameTyped s {f with code := after, vals := front ++ [value]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ operands)) code
    have principal := signature.principal instruction
    simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
    rcases principal with ⟨rfl,rfl⟩
    simp only [List.map_append,types,List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    have resultTyped := numeric_value_typed signature.output_numeric storeWf effect.wf effect.2
    apply FrameTyped.mk (f := {f with code := after, vals := front ++ [value]}) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,effect.2] using
        List.rel_append frontTyped (List.Forall₂.cons resultTyped List.Forall₂.nil)
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,effect.2,stack] using continuation

theorem PureSignature.typed_operands {source inputs output}
    (signature : PureSignature source inputs output) {s : store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s {f with code := source :: after} []) :
    ∃ front operands, f.vals = front ++ operands ∧ ResultsTyped s inputs operands ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,_,_,operation,values,operandTypes,valid,heights⟩ :=
    frame_typed_operands_bounds typed
  have principal := signature.principal operation
  simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
  rcases principal with ⟨rfl,rfl⟩
  exact ⟨front,operands,values,operandTypes,valid,heights⟩

theorem PureSignature.prefix_bounds {source inputs output}
    (signature : PureSignature source inputs output) {s : store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s {f with code := source :: after} [])
    {front operands : List val} (values : f.vals = front ++ operands)
    (types : operands.map valueType = inputs) :
    Forall wf_val front ∧ Forall wf_val operands ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨other,actual,split,actualTyped,_,heights⟩ := signature.typed_operands typed
  have equal : other.length = front.length := by
    have first := congrArg List.length split
    have second := congrArg List.length values
    have size := congrArg List.length types
    have actualSize := results_typed_length actualTyped
    simp only [List.length_append,List.length_map] at first second size
    omega
  have valid := (frame_typed_wf typed).2.2.1
  change Forall wf_val f.vals at valid
  rw [values] at valid
  exact ⟨fun v hv => valid v (List.mem_append_left _ hv),
    fun v hv => valid v (List.mem_append_right _ hv),by simpa only [equal] using heights⟩

/-- Pure SIMD changes only the active operand stack and source cursor. -/
inductive Transition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (source : instr) (inputs : List valtype) (output : valtype) : AState → Prop where
  | next (front operands : List val) (value : val)
      (values : f.vals = front ++ operands) (types : operands.map valueType = inputs)
      (effect : PureResult source output operands value) :
      Transition s f rest after source inputs output
        ⟨s.store,s.ambient,{f with code := after, vals := front ++ [value]} :: rest,[]⟩

theorem transition_preservation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState}
    (signature : PureSignature source inputs output)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : ATyped next := by
  cases step with
  | next front operands value values types effect =>
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    apply active_frame_preservation typed
      (signature.frame_preservation front operands value types typed.store effect ?_) rfl
    change f.vals = front ++ operands at values
    simpa only [values] using hf

theorem transition_simulation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState}
    (signature : PureSignature source inputs output)
    (typed : ATyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) :
    NextSim ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩ next := by
  cases step with
  | next front operands value values types effect =>
    change f.vals = front ++ operands at values
    have hf : FrameTyped s {f with code := source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frame_typed_wf hf
    obtain ⟨frontWf,operandsWf,heights⟩ := signature.prefix_bounds hf values types
    have simulated := pure_stack_simulation s ambient f rest source after front operands [value]
      typed.store typed.ambient frameWf labelsWf frontWf
      (fun op member => codeWf op (by simp [member])) hr heights operandsWf
      (by intro v member; have eq := List.mem_singleton.mp member; subst v; exact effect.wf)
      (codeWf source (by simp)) effect.1
    apply NextSim.single
    simpa only [values] using simulated

end Itasca.Runtime.SourceMachine.Simd

end

/-! ## MemoryTransition -/

section

/-!
SIMD memory transition typing and source simulation. Pure SIMD transition and shared memory mutation contracts remain separate.
-/

/-! ## Memory Typing -/

section

namespace Itasca.Runtime.SourceMachine.Simd
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
      code_stack_after (value_types_concrete (front ++ operands)) code
    have principal := signature.principal instruction
    simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
    rcases principal with ⟨rfl,rfl⟩
    simp only [List.map_append,types,List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
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
      ⟨memory_payload_write_extends before frame address start object payload storeWf contents mapped found valid,
       contents.memory_write storeWf frame address start object payload mapped found valid⟩

end Itasca.Runtime.SourceMachine.Simd

end

/-! ## Memory Transition -/

section

namespace Itasca.Runtime.SourceMachine.Simd
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
      have wf := (wf_config_parts (step_h_wf effect).2).2
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
    have actualSize := results_typed_length actualTyped
    simp only [List.length_append,List.length_map] at first second size
    omega
  have valid := (frame_typed_wf typed).2.2.1
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
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨_,labelsWf,_,codeWf⟩ := frame_typed_wf hf
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
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frame_typed_wf hf
    obtain ⟨frontWf,heights⟩ := signature.prefix_bounds hf values types
    have simulated := operand_trap_simulation s ambient f rest source after front operands
      typed.store typed.ambient frameWf labelsWf frontWf
      (fun op member => codeWf op (by simp [member])) hr heights effect
    simpa only [values] using simulated

end Itasca.Runtime.SourceMachine.Simd

end

end
