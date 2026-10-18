import Exec.Store.Api.MemoryGrowExtension
import Exec.Store.Api.TableGrowExtension
import Exec.Store.Api.Write
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Actual public memory growth preserves source/structural validity and the
generated store-extension relation on every normal outcome. -/
theorem memory_grow_api_extends {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (index : Usize) (delta : U32) (inBounds : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_with ops s ⟨s.id, index⟩ delta ⦃ answer =>
      Shape view answer.2 ∧ StoreSyntax code answer.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code answer.2) ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step with memory_grow_extends ops view laws code s shape sourceSyntax index delta inBounds
    as ⟨result, after, freshShape, freshSyntax, extension⟩
  exact ⟨freshShape, freshSyntax, extension⟩

/-- Public table growth preserves the decoded extension relation, including
allocator refusal and the successful maximal-size zero-growth boundary. -/
theorem table_grow_api_extends {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (inBounds : index.val < s.tables.length)
    (typed : elementValueType (s.tables.val[index.val]).ty = Interp.rawType value)
    (owned : ValueInStore s value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value ⦃ answer =>
      Shape view answer.2 ∧ StoreSyntax code answer.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code answer.2) ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value owned.1]
  simp
  step as ⟨table, found⟩
  simp [found, typed, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  step with encode_reference_shape s value (s.tables.val[index.val]).ty typed owned as ⟨lo, hi, canonical⟩
  step with table_grow_extends ops allocator allocation view code s shape sourceSyntax index delta lo inBounds canonical
    as ⟨result, after, freshShape, freshSyntax, extension⟩
  exact ⟨freshShape, freshSyntax, extension⟩
end Exec.Store
