import Itasca.Runtime.Abs.Simd.MemoryTyping
import Itasca.Runtime.Abs.Core.Trap

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
