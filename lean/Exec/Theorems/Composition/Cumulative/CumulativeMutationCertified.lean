import Exec.Store.Initialization.SegmentCounts
import Exec.Theorems.Composition.Certified.CertifiedCumulativeContent
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Theorems.Composition.Stateful.StatefulOwnership
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- An internal dispatch witness, established from exact runtime mutation
footprints. Segment contents may change; their checked bounds remain explicit. -/
structure CumulativeStoreMutation {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M) : Prop where
  metadata : Interp.FrameStoreMetadata before after
  externs : after.externs = before.externs
  shape : Store.Shape view after
  segmentBounds : Store.SegmentBounds after
  extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after
  limits : after.limits = before.limits

/-- Fresh object contents preserve all static cumulative code certificates.
Unlike ordinary scalar updates, this also admits segment drops and growth. -/
theorem CertifiedCumulativeStore.update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedCumulativeStore view code after := by
  have syntaxAfter : Store.StoreSyntax code after := by
    simpa only [Store.StoreSyntax, mutation.metadata.instances] using certified.storeSyntax
  have decodedFunctions : (Store.decodeStore view code after).FUNCS =
      (Store.decodeStore view code before).FUNCS := by
    have decodeFunction : Store.decodeFunction code after = Store.decodeFunction code before := by
      funext function
      simp only [Store.decodeFunction, Store.decodeInstance, mutation.metadata.types, mutation.metadata.instances]
    simp only [Store.decodeStore, mutation.metadata.functions, decodeFunction]
  exact ⟨mutation.shape, syntaxAfter,
    Store.core_functions_typed_metadata mutation.metadata.functions mutation.metadata.types mutation.metadata.instances
      mutation.extension certified.typed,
    certified.core.same decodedFunctions,
    Store.cumulative_compiled_functions_metadata code mutation.metadata.identity mutation.metadata.functions
      mutation.metadata.types mutation.metadata.instances certified.compiled,
    mutation.segmentBounds⟩

theorem CumulativeStoreMutation.ownership_bounds {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) :
    Store.ownershipBounds after = Store.ownershipBounds before := by
  unfold Store.ownershipBounds
  rw [mutation.metadata.functions,mutation.externs]

theorem CumulativeStoreMutation.refl {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code store) :
    CumulativeStoreMutation view code store store :=
  ⟨.refl store, rfl, certified.shape, certified.segmentBounds,
    Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),.refl store,rfl⟩

theorem CumulativeStoreMutation.trans {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {a b c : runtime.store.Store M}
    (first : CumulativeStoreMutation view code a b) (second : CumulativeStoreMutation view code b c) :
    CumulativeStoreMutation view code a c :=
  ⟨first.metadata.trans second.metadata,second.externs.trans first.externs,second.shape,second.segmentBounds,
    Spec.extend_store_trans first.extension second.extension,first.segmentCounts.trans second.segmentCounts,second.limits.trans first.limits⟩
end Exec.Theorems
