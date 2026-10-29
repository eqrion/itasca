import Itasca.Runtime.SourceMachine.Simd.Transition
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Simd.MemoryTransition
import Itasca.Runtime.SourceMachine.SupportedState

/-!
SIMD step invariant preservation, combining constants and memory operations with support coverage. Primitive transition contracts remain below this composition.
-/

/-! ## Invariants -/

section

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec Ownership

theorem numeric_value_owned {value : val} {output : valtype}
    (numeric : output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty)
    (typeEq : valueType value = output) (bounds : Bounds) : ValueOwned bounds value := by
  cases value with
  | CONST | VCONST | REF_NULL => trivial
  | REF_FUNC_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]
  | REF_HOST_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]

theorem transition_owned {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState} {bounds}
    (signature : PureSignature source inputs output)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : StatefulOwned bounds next := by
  cases step with
  | next front operands value values types effect =>
    have active := owned.values.2 _ (List.mem_cons_self ..)
    change FrameOwned bounds f at active
    change f.vals = front ++ operands at values
    refine ⟨⟨valuesOwned_nil _,?_⟩,owned.heap⟩
    intro item member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨active.1,valuesOwned_append.mpr ⟨?_,?_⟩⟩
      · have before := active.2
        rw [values] at before
        exact (valuesOwned_append.mp before).1
      · exact valuesOwned_cons.mpr ⟨numeric_value_owned signature.output_numeric effect.2 bounds,valuesOwned_nil _⟩
    · exact owned.values.2 item (List.mem_cons_of_mem _ member)

theorem transition_core_typed {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState}
    (signature : PureSignature source inputs output)
    (typed : CoreTyped ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : CoreTyped next := by
  have preserved := transition_preservation signature typed.typed step
  cases step
  exact ⟨preserved,typed.contents⟩

theorem transition_bound {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs output} {next : AState} {bound}
    (bounded : CodeBound bound ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs output next) : CodeBound bound next := by
  cases step with
  | next front operands value values types effect =>
    apply bound_replace_frame bounded
    have active := bounded.frames _ (List.mem_cons_self ..)
    refine ⟨?_,active.2⟩
    have size : sizeOf after < sizeOf (source :: after) := by simp
    exact Nat.le_trans (Nat.le_of_lt size) active.1

end Itasca.Runtime.Abs.Simd

end

/-! ## Constant -/

section

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec Ownership

def constant (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) (value : vec_) : AState :=
  ⟨s.store,s.ambient,{f with code := after, vals := f.vals ++ [.VCONST .V128 value]} :: rest,[]⟩

theorem constant_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {value : vec_} (storeWf : wf_store s)
    (typed : FrameTyped s {f with code := .VCONST .V128 value :: after} []) :
    FrameTyped s {f with code := after, vals := f.vals ++ [.VCONST .V128 value]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    have instructionWf := codeStack_wf code (.VCONST .V128 value) (by simp)
    have resultWf : wf_val (.VCONST .V128 value) := by
      cases instructionWf
      constructor <;> assumption
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      codeStack_after (value_types_concrete f.vals) code
    cases instruction
    simp only [List.append_nil] at stack
    have resultTyped := Val_ok.vectype s .V128 value storeWf resultWf
    apply FrameTyped.mk (f := {f with code := after, vals := f.vals ++ [.VCONST .V128 value]}) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa [ResultsTyped,List.map_append,valueType,valtype_vectype] using
        List.rel_append values (List.Forall₂.cons resultTyped List.Forall₂.nil)
    · simpa [List.map_append,valueType,stack] using continuation

theorem constant_typed {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_}
    (typed : CoreTyped ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    CoreTyped (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  have hf : FrameTyped s {f with code := .VCONST .V128 value :: after} [] := by
    cases typed.typed.frames with | cons h _ => exact h
  exact ⟨active_frame_preservation typed.typed (constant_frame_preservation typed.typed.store hf) rfl,typed.contents⟩

theorem constant_simulation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_}
    (typed : ATyped ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    NextSim ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩
      (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  have hf : FrameTyped s {f with code := .VCONST .V128 value :: after} [] := by
    cases typed.frames with | cons h _ => exact h
  have heights := frameTyped_heights hf
  apply Or.inl
  constructor
  · simp only [constant,decode,decodeFrames,vals,List.map_nil,List.nil_append,
      AFrame.toFrame,List.map_cons,admininstr_instr]
    rw [decodeLabels_move_values _ _ _ _ heights]
    rfl
  · simp [constant,administrativeMeasure]

theorem constant_owned {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_} {bounds}
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    StatefulOwned bounds (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  refine ⟨⟨valuesOwned_nil _,?_⟩,owned.heap⟩
  intro item member
  simp only [constant,List.mem_cons] at member
  rcases member with rfl | member
  · have active := owned.values.2 _ (List.mem_cons_self ..)
    exact ⟨active.1,valuesOwned_append.mpr ⟨active.2,by simp [ValuesOwned,ValueOwned]⟩⟩
  · exact owned.values.2 item (List.mem_cons_of_mem _ member)

theorem constant_bound {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_} {bound}
    (bounded : CodeBound bound ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    CodeBound bound (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  apply bound_replace_frame bounded
  have active := bounded.frames _ (List.mem_cons_self ..)
  refine ⟨?_,active.2⟩
  have size : sizeOf after < sizeOf (instr.VCONST .V128 value :: after) := by simp
  exact Nat.le_trans (Nat.le_of_lt size) active.1

end Itasca.Runtime.Abs.Simd

end

/-! ## Memory Invariants -/

section

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec Ownership

theorem MemorySignature.results_owned {source inputs outputs}
    (signature : MemorySignature source inputs outputs) {values : List val}
    (types : values.map valueType = outputs) (bounds : Bounds) : ValuesOwned bounds values := by
  have vectorResults {values : List val} (types : values.map valueType = [.V128]) :
      ValuesOwned bounds values := by
    cases values with
    | nil => simp at types
    | cons value tail =>
      simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at types
      rcases types with ⟨typeEq,rfl⟩
      exact valuesOwned_cons.mpr ⟨numeric_value_owned (Or.inl rfl) typeEq bounds,valuesOwned_nil _⟩
  cases signature
  all_goals first
    | exact vectorResults types
    | have empty := List.map_eq_nil_iff.mp types; subst values; exact valuesOwned_nil _

theorem MemoryChange.heap_owned {before frame after bounds}
    (change : MemoryChange before frame after) (owned : StatefulHeapOwned bounds before) :
    StatefulHeapOwned bounds after := by
  cases change <;> exact ⟨owned.globals,owned.tables,owned.elements,owned.functions⟩

theorem memory_transition_owned {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs} {next : AState} {bounds}
    (signature : MemorySignature source inputs outputs)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs (.next next)) :
    StatefulOwned bounds next := by
  cases step with
  | next front operands results store values types resultTypes change effect =>
    have active := owned.values.2 _ (List.mem_cons_self ..)
    change FrameOwned bounds f at active
    change f.vals = front ++ operands at values
    refine ⟨⟨valuesOwned_nil _,?_⟩,change.heap_owned owned.heap⟩
    intro item member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨active.1,valuesOwned_append.mpr ⟨?_,signature.results_owned resultTypes bounds⟩⟩
      have before := active.2
      rw [values] at before
      exact (valuesOwned_append.mp before).1
    · exact owned.values.2 item (List.mem_cons_of_mem _ member)

theorem memory_transition_bound {s : _root_.store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {source inputs outputs} {next : AState} {bound}
    (bounded : CodeBound bound ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩)
    (step : MemoryTransition ⟨s,ambient,{f with code := source :: after} :: rest,[]⟩
      {f with code := source :: after} rest after source inputs outputs (.next next)) :
    CodeBound bound next := by
  cases step with
  | next front operands results store values types resultTypes change effect =>
    refine ⟨bounded.positive,?_,?_⟩
    · intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · have active := bounded.frames _ (List.mem_cons_self ..)
        refine ⟨?_,active.2⟩
        have size : sizeOf after < sizeOf (source :: after) := by simp
        exact Nat.le_trans (Nat.le_of_lt size) active.1
      · exact bounded.frames item (List.mem_cons_of_mem _ member)
    · change ∀ fn ∈ store.FUNCS, _
      rw [change.functions]
      exact bounded.functions

end Itasca.Runtime.Abs.Simd

end

/-! ## Step -/

section

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec Ownership

/-- Relational SIMD execution, preserving source nondeterminism in pure results
and exact payload mutations for memory operations. -/
inductive Step : AState → AResult → Prop where
  | pure {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs output next}
      (signature : PureSignature source inputs output)
      (transition : Transition ⟨s,ambient,{f with code := source :: after}::rest,[]⟩
        {f with code := source :: after} rest after source inputs output next) :
      Step ⟨s,ambient,{f with code := source :: after}::rest,[]⟩ (.next next)
  | constant {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {value : vec_} :
      Step ⟨s,ambient,{f with code := .VCONST .V128 value :: after}::rest,[]⟩
        (.next (Simd.constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after}::rest,[]⟩ f rest after value))
  | memory {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs outputs result}
      (signature : MemorySignature source inputs outputs)
      (transition : MemoryTransition ⟨s,ambient,{f with code := source :: after}::rest,[]⟩
        {f with code := source :: after} rest after source inputs outputs result) :
      Step ⟨s,ambient,{f with code := source :: after}::rest,[]⟩ result

theorem Step.next_typed {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : CoreTyped next := by
  cases step with
  | pure signature transition => exact transition_core_typed signature typed transition
  | constant => exact constant_typed typed
  | memory signature transition => exact (memory_transition_preservation signature typed transition).1

theorem Step.next_simulation {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : NextSim before next := by
  cases step with
  | pure signature transition => exact transition_simulation signature typed.typed transition
  | constant => exact constant_simulation typed.typed
  | memory signature transition => exact memory_transition_simulation signature typed.typed transition

theorem Step.next_owned {before next bounds} (step : Step before (.next next))
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | pure signature transition => exact transition_owned signature owned transition
  | constant => exact constant_owned owned
  | memory signature transition => exact memory_transition_owned signature owned transition

theorem Step.next_bound {before next bound} (step : Step before (.next next))
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | pure signature transition => exact transition_bound bounded transition
  | constant => exact constant_bound bounded
  | memory signature transition => exact memory_transition_bound bounded transition

theorem Step.next_extension {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : Extend_store before.store next.store := by
  cases step with
  | pure signature transition => cases transition; exact extend_store_refl _ typed.typed.store
  | constant => exact extend_store_refl _ typed.typed.store
  | memory signature transition => exact (memory_transition_preservation signature typed transition).2

theorem Step.trap_simulation {before} (step : Step before .trap) (typed : CoreTyped before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | memory signature transition => exact memory_transition_trap_simulation signature typed.typed transition

end Itasca.Runtime.Abs.Simd

end

/-! ## Coverage -/

section

namespace Itasca.Runtime.Abs.Simd

/-- SIMD consumes its source head without changing any remaining source syntax.
The argument is independent of the eventual cumulative instruction family. -/
theorem Step.next_supported {before next}
    (step : Step before (.next next)) (covered : SupportedState before) :
    SupportedState next := by
  cases step with
  | pure signature transition =>
    cases transition
    exact covered.tail rfl _
  | constant => exact covered.tail rfl _
  | memory signature transition =>
    cases transition with
    | next front operands results store values types resultTypes change effect =>
      exact covered.tail change.functions _

end Itasca.Runtime.Abs.Simd

end
