import Exec.Store.Api.GlobalWriteExtension
import Exec.Interp.Core.Mutation
import Exec.Theorems.Composition.Core.CoreMemoryInstructionCertified
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Spec.Mutation
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Store Exec.Interp

theorem global_mutation_core_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedCoreStore view code before) (value : val)
    (mutation : GlobalMutation before after value) (wellFormed : wf_val value)
    (owned : Abs.Ownership.ValueOwned (ownershipBounds before) value) :
    CertifiedCoreStore view code after ∧
      Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have shape := global_mutation_shape certified.shape mutation wellFormed owned
  obtain ⟨index,old,lo,hi,issued,mutable,typed,represented,high,rfl⟩ := mutation
  have sourceSyntax : StoreSyntax code {before with globals := before.globals.set index {old with lo,hi}} := certified.storeSyntax
  have oldWf := decodeStore_wf view code before certified.shape certified.storeSyntax
  have newWf := decodeStore_wf view code _ shape sourceSyntax
  have objectExtension : Extend_globalinst (decodeGlobal old) (decodeGlobal {old with lo,hi}) := by
    unfold decodeGlobal
    rw [mutable]
    exact Spec.extend_global_mutable _ _ _
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
  have extension : Extend_store (decodeStore view code before)
      (decodeStore view code {before with globals := before.globals.set index {old with lo,hi}}) := by
    rw [decodeStore_global_update view code before (before.globals.set index {old with lo,hi})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_global _ _ _ oldWf
    · simpa only [decodeStore] using newWf
    · intro bound
      have position := (List.getElem?_eq_some_iff.mp issued).1
      have actual := (List.getElem?_eq_some_iff.mp issued).2
      simpa only [decodeStore,getElem!_pos (before.globals.val.map decodeGlobal) index.val
        (by simpa only [List.length_map] using position),List.getElem_map,actual] using objectExtension
  exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,extension⟩

/-- Exact mutation footprints, current ownership and current certification
suffice to re-establish all raw and decoded store invariants after a dispatch. -/
theorem core_mutation_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M) (source : Abs.AState)
    (certified : CertifiedCoreStore view code before)
    (owned : Abs.Ownership.CoreOwned (ownershipBounds before) source)
    (mutation : CoreStoreMutation view source before after) :
    CertifiedCoreStore view code after ∧
      Extend_store (decodeStore view code before) (decodeStore view code after) ∧
      ownershipBounds after = ownershipBounds before := by
  have bounds : ownershipBounds after = ownershipBounds before := by
    unfold ownershipBounds
    rw [mutation.metadata.functions,mutation.externs]
  refine ⟨?_,?_,bounds⟩
  all_goals
    cases mutation with
    | unchanged =>
      first | exact certified | exact Spec.extend_store_refl _ (decodeStore_wf view code before certified.shape certified.storeSyntax)
    | memory issued mutation =>
      have preserved := memory_mutation_core_certified view code before _ certified _ _ issued mutation
      first | exact preserved.1 | exact preserved.2
    | global live wellFormed mutation =>
      have preserved := global_mutation_core_certified view code before _ certified _ mutation wellFormed (live.owned owned)
      first | exact preserved.1 | exact preserved.2
end Exec.Theorems
