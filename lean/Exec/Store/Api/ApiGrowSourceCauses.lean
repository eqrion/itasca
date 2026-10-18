import Exec.Store.Api.GrowSourceCauses
import Exec.Store.Api.Write
namespace Exec.Store
open Aeneas Aeneas.Std
theorem table_grow_api_source_cause {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (index : Usize) (delta : U32) (value : runtime.Value)
    (issued : index.val < s.tables.length)
    (typed : elementValueType (s.tables.val[index.val]).ty = Interp.rawType value)
    (owned : ValueInStore s value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value ⦃ result =>
      result.1 = .Ok core.num.U32.MAX → ∃ table,
        s.tables.val[index.val]? = some table ∧
        (SourceGrowthLimit (decodeTable table).REFS.length delta.val U32.max
          ((decodeStore view code s).TABLES.map fun t => t.REFS.length).sum
          s.limits.max_table_elements.val 1 (tableMaximum (decodeTable table)) ∨
        allocator.reserve table.elements (UScalar.cast .Usize delta) = .ok (false, table.elements) ∨
        ((decodeTable table).REFS.length = U32.max ∧ delta.val = 0)) ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value owned.1]
  simp
  step as ⟨table, found⟩
  simp [found, typed, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  step with encode_reference_shape s value (s.tables.val[index.val]).ty typed owned as ⟨lo, hi, canonical⟩
  step with table_grow_source_cause ops allocator law view code s shape index delta lo issued
    as ⟨result, after, cause⟩
  simpa using cause

theorem memory_grow_api_source_cause {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (code : CodeInterpretation) (s : runtime.store.Store M) (shape : Shape view s)
    (index : Usize) (delta : U32) (issued : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_with ops s ⟨s.id, index⟩ delta ⦃ result =>
      result.1 = .Ok core.num.U32.MAX → ∃ m,
        s.memories.val[index.val]? = some m ∧
        (SourceGrowthLimit ((decodeMemory view m).BYTES.length / 65536) delta.val 65536
          ((decodeStore view code s).MEMS.map fun memory => memory.BYTES.length).sum
          s.limits.max_memory_bytes.val 65536 (memoryMaximum (decodeMemory view m)) ∨
        ∃ requested : Usize, ∃ after : M,
          requested.val = ((decodeMemory view m).BYTES.length / 65536 + delta.val) * 65536 ∧
          ops.grow m.buf requested = .ok (false, after)) ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step with memory_grow_source_cause ops view laws code s shape index delta issued
    as ⟨result, after, cause⟩
  simpa using cause
end Exec.Store
