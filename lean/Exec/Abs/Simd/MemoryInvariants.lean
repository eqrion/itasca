import Exec.Abs.Simd.MemoryTransition
import Exec.Abs.Simd.Invariants

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
