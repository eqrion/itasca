import Exec.Store.Api.TableGrowRefusal
import Exec.Store.Api.MemoryGrowRefusal
namespace Exec.Store
open Aeneas Aeneas.Std

def tableMaximum (table : tableinst) : Option Nat :=
  match table.TYPE with
  | .mk_tabletype (.mk_limits _ maximum) _ => maximum.map fun | .mk_uN n => n

def memoryMaximum (memory : meminst) : Option Nat :=
  match memory.TYPE with
  | .PAGE (.mk_limits _ maximum) => maximum.map fun | .mk_uN n => n

/-- Every limit in this predicate is a decoded object size, source maximum,
intrinsic Wasm ceiling, or configured aggregate store budget. -/
def SourceGrowthLimit (old delta ceiling total budget unit : Nat) (maximum : Option Nat) : Prop :=
  ceiling < old + delta ∨ (∃ bound, maximum = some bound ∧ bound < old + delta) ∨
    budget < total + delta * unit

private theorem length_le_total {α : Type} (size : α → Nat) {a : α} {xs : List α}
    (member : a ∈ xs) : size a ≤ (xs.map size).sum := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    simp only [List.mem_cons] at member
    simp only [List.map_cons, List.sum_cons]
    rcases member with rfl | member
    · omega
    · have := ih member; omega

theorem table_grow_source_cause {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (index : Usize) (delta : U32) (value : U64)
    (issued : index.val < s.tables.length) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result =>
      result.1 = core.num.U32.MAX → ∃ table,
        s.tables.val[index.val]? = some table ∧
        (SourceGrowthLimit (decodeTable table).REFS.length delta.val U32.max
          ((decodeStore view code s).TABLES.map fun t => t.REFS.length).sum
          s.limits.max_table_elements.val 1 (tableMaximum (decodeTable table)) ∨
        allocator.reserve table.elements (UScalar.cast .Usize delta) = .ok (false, table.elements) ∨
        ((decodeTable table).REFS.length = U32.max ∧ delta.val = 0)) ⦄ := by
  apply WP.spec_mono (table_grow_refusal ops allocator law s index delta value issued
    (fun t ht => (shape.tables t ht).1))
  intro result post sentinel
  obtain ⟨table, found, refusal | boundary⟩ := post sentinel
  · refine ⟨table, found, ?_⟩
    rcases refusal with ceiling | maximum | budget | allocation
    · exact Or.inl (Or.inl (by simpa [decodeTable] using ceiling))
    · cases h : table.maximum with
      | none =>
        left; left
        simpa [h, core.option.Option.unwrap_or, decodeTable, U32.max_eq, U32.rMax] using maximum
      | some bound =>
        left; right; left
        exact ⟨bound.val, by simp [tableMaximum, decodeTable, decodeLimits, h],
          by simpa [h, core.option.Option.unwrap_or, decodeTable] using maximum⟩
    · left; right; right
      simpa [decodeStore, decodeTable, List.map_map, Function.comp_def, ← shape.tableAccounting] using budget
    · exact Or.inr (Or.inl allocation)
  · exact ⟨table, found, Or.inr (Or.inr (by simpa [decodeTable] using boundary))⟩
theorem memory_grow_source_cause {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (code : CodeInterpretation) (s : runtime.store.Store M) (shape : Shape view s)
    (index : Usize) (delta : U32) (issued : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result =>
      result.1 = core.num.U32.MAX → ∃ m,
        s.memories.val[index.val]? = some m ∧
        (SourceGrowthLimit ((decodeMemory view m).BYTES.length / 65536) delta.val 65536
          ((decodeStore view code s).MEMS.map fun memory => memory.BYTES.length).sum
          s.limits.max_memory_bytes.val 65536 (memoryMaximum (decodeMemory view m)) ∨
        ∃ requested : Usize, ∃ after : M,
          requested.val = ((decodeMemory view m).BYTES.length / 65536 + delta.val) * 65536 ∧
          ops.grow m.buf requested = .ok (false, after)) ⦄ := by
  apply WP.spec_mono (memory_grow_refusal ops view laws s index delta issued
    (fun m hm => (shape.memories m hm).length_bound))
  intro result post sentinel
  obtain ⟨m, found, refusal⟩ := post sentinel
  refine ⟨m, found, ?_⟩
  have member := List.mem_of_getElem? found
  have memoryShape := shape.memories m member
  have individual : (view m.buf).length ≤ s.memory_bytes.val := by
    rw [shape.memoryAccounting]
    exact length_le_total (fun memory => (view memory.buf).length) member
  have aligned := memoryShape.1
  have limitBound : s.limits.max_memory_bytes.val ≤ Usize.max := by scalar_tac
  have aggregate : ((decodeStore view code s).MEMS.map fun memory => memory.BYTES.length).sum =
      s.memory_bytes.val := by
    simp [decodeStore, decodeMemory, decodeBytes, List.map_map, Function.comp_def, shape.memoryAccounting]
  have bytesEq : (decodeMemory view m).BYTES.length = (view m.buf).length := by
    simp [decodeMemory, decodeBytes]
  rcases refusal with ceiling | maximum | addOverflow | newOverflow | budget | refused
  · left; left; simpa [bytesEq] using ceiling
  · cases h : m.maximum with
    | none =>
      left; left
      simpa [h, core.option.Option.unwrap_or, bytesEq] using maximum
    | some bound =>
      left; right; left
      exact ⟨bound.val, by simp [memoryMaximum, decodeMemory, decodeLimits, h],
        by simpa [h, core.option.Option.unwrap_or, bytesEq] using maximum⟩
  · left; right; right
    rw [aggregate]
    omega
  · left; right; right
    rw [aggregate]
    have divide := Nat.mod_add_div (view m.buf).length 65536
    omega
  · left; right; right
    simpa [aggregate] using budget
  · right
    simpa [bytesEq] using refused
end Exec.Store
