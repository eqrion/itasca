import Exec.Theorems.Composition.Certified.CertifiedFloatCoreContent
import Exec.Theorems.Composition.Core.CoreMutationCertified
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- A byte-length-preserving instruction update retains the current executable
store certificate. -/
theorem memory_mutation_float_core_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedFloatCoreStore view code before)
    (address : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (issued : before.memories.val[address.index.val]? = some object)
    (mutation : Interp.MemoryMutation view before after address object) :
    CertifiedFloatCoreStore view code after ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  have inBounds : address.index.val < before.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  have found : before.memories.val[address.index.val] = object := (List.getElem?_eq_some_iff.mp issued).2
  let after := {before with memories := before.memories.set address.index {object with buf := buffer}}
  have shape : Store.Shape view after := by
    apply certified.shape.memory_replace_same_length address.index inBounds
    · simpa only [found] using lengthEq
    · simp only [found]
  have sourceSyntax : Store.StoreSyntax code after := certified.storeSyntax
  have oldWf := Store.decodeStore_wf view code before certified.shape certified.storeSyntax
  have newWf := Store.decodeStore_wf view code after shape sourceSyntax
  have oldMemoryWf : wf_meminst (Store.decodeMemory view object) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (certified.shape.memories object (List.mem_of_getElem? issued)).2.1
      scalar_tac
    · exact Store.decodeBytes_wf _
  have newMemoryWf : wf_meminst (Store.decodeMemory view {object with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (certified.shape.memories object (List.mem_of_getElem? issued)).2.1
      simp only [lengthEq]
      scalar_tac
    · exact Store.decodeBytes_wf _
  have objectExtension := Store.decodeMemory_extends view object {object with buf := buffer}
    rfl (Nat.le_of_eq lengthEq.symm) oldMemoryWf newMemoryWf
  have extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
    unfold after at newWf ⊢
    rw [Store.decodeStore_memory_update view code before
      (before.memories.set address.index {object with buf := buffer})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf
    · simpa only [Store.decodeStore] using newWf
    · intro bound
      simpa only [Store.decodeStore,found,
        getElem!_pos (before.memories.val.map (Store.decodeMemory view)) address.index.val
          (by simpa only [List.length_map] using inBounds),List.getElem_map] using objectExtension
  exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
    extension⟩

theorem global_mutation_float_core_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedFloatCoreStore view code before) (value : val)
    (mutation : GlobalMutation before after value) (wellFormed : wf_val value)
    (owned : Abs.Ownership.ValueOwned (ownershipBounds before) value) :
    CertifiedFloatCoreStore view code after ∧
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
theorem float_core_mutation_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M) (source : Abs.AState)
    (certified : CertifiedFloatCoreStore view code before)
    (owned : Abs.Ownership.CoreOwned (ownershipBounds before) source)
    (mutation : CoreStoreMutation view source before after) :
    CertifiedFloatCoreStore view code after ∧
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
      have preserved := memory_mutation_float_core_certified view code before _ certified _ _ issued mutation
      first | exact preserved.1 | exact preserved.2
    | global live wellFormed mutation =>
      have preserved := global_mutation_float_core_certified view code before _ certified _ mutation wellFormed (live.owned owned)
      first | exact preserved.1 | exact preserved.2
end Exec.Theorems
