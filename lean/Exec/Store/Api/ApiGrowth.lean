import Exec.Store.Api.GrowthInvariant
import Exec.Store.Api.Write

namespace Exec.Store
open Aeneas Aeneas.Std

theorem memory_grow_api_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hs : Shape view s) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_with ops s ⟨s.id, index⟩ delta ⦃ answer => Shape view answer.2 ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step with memory_grow_preserves_shape ops view laws code s hs index delta hindex as ⟨result, after, hresult⟩
  simpa using hresult

theorem table_grow_api_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (hindex : index.val < s.tables.length)
    (htype : elementValueType (s.tables.val[index.val]).ty = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value ⦃ answer => Shape view answer.2 ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv.1]
  simp
  step as ⟨table, htable⟩
  simp [htable, htype, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  step with encode_reference_shape s value (s.tables.val[index.val]).ty htype hv as ⟨lo, hi, hwords⟩
  step with table_grow_preserves_shape ops allocator ha view s hs index delta lo hindex hwords as ⟨result, after, hresult⟩
  simpa using hresult

end Exec.Store
