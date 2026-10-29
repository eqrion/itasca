import Itasca.Runtime.SourceMachine.Simd.Signature
import Itasca.Runtime.SourceMachine.Sim.Typed
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.Spec.PureWf

namespace Itasca.Runtime.Abs.Simd
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
      codeStack_after (value_types_concrete (front ++ operands)) code
    have principal := signature.principal instruction
    simp only [functype.mk_functype.injEq,list.mk_list.injEq] at principal
    rcases principal with ⟨rfl,rfl⟩
    simp only [List.map_append,types,List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using resultsTyped_take front.length values
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
    have actualSize := resultsTyped_length actualTyped
    simp only [List.length_append,List.length_map] at first second size
    omega
  have valid := (frameTyped_wf typed).2.2.1
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
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨frameWf,labelsWf,_,codeWf⟩ := frameTyped_wf hf
    obtain ⟨frontWf,operandsWf,heights⟩ := signature.prefix_bounds hf values types
    have simulated := pure_stack_simulation s ambient f rest source after front operands [value]
      typed.store typed.ambient frameWf labelsWf frontWf
      (fun op member => codeWf op (by simp [member])) hr heights operandsWf
      (by intro v member; have eq := List.mem_singleton.mp member; subst v; exact effect.wf)
      (codeWf source (by simp)) effect.1
    apply NextSim.single
    simpa only [values] using simulated

end Itasca.Runtime.Abs.Simd
