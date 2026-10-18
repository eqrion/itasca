import Exec.Store.Api.GrowthLimits
import Exec.Theorems.Composition.Cumulative.CumulativeMutationCertified
import Exec.Store.Api.GrowthEffects
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Store

/-- The exact growth footprint supplies raw invariants; the chosen typed source
transition supplies store extension at the execution join. -/
theorem memory_growth_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index : Usize} {delta out}
    (certified : CertifiedCumulativeStore view code before)
    (issued : index.val < before.memories.length)
    (effect : MemoryGrowth view code before index delta out)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code out.2)) :
    CumulativeStoreMutation view code before out.2 := by
  obtain ⟨metadata,externs,elements,datas⟩ := effect.metadata
  exact ⟨metadata,externs,effect.shape view code before certified.shape index delta issued out,
    ⟨by simpa only [elements] using certified.segmentBounds.elements,
     by simpa only [datas] using certified.segmentBounds.data⟩,extension,⟨by rw [elements],by rw [datas]⟩,effect.limits⟩

theorem table_growth_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index : Usize} {delta value out}
    (certified : CertifiedCumulativeStore view code before)
    (issued : index.val < before.tables.length)
    (owned : ReferenceShape before (before.tables.val[index.val]).ty value)
    (effect : TableGrowth before index delta value out)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code out.2)) :
    CumulativeStoreMutation view code before out.2 := by
  obtain ⟨metadata,externs,elements,datas⟩ := effect.metadata
  exact ⟨metadata,externs,effect.shape view before certified.shape index delta value issued owned out,
    ⟨by simpa only [elements] using certified.segmentBounds.elements,
     by simpa only [datas] using certified.segmentBounds.data⟩,extension,⟨by rw [elements],by rw [datas]⟩,effect.limits⟩
end Exec.Theorems
