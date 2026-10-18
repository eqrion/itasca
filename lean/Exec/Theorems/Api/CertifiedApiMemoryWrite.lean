import Exec.Theorems.Api.CertifiedApi
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Invariant.ObjectExtension
import Exec.Store.Api.Api
namespace Exec.Theorems.CertifiedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Returning a borrowed mutable memory slice with its original length retains
all execution certificates and extends the decoded specification store. -/
theorem memory_write_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (inBounds : index.val < store.memories.length) :
    runtime.store.Store.memory_mut memory store ⟨store.id, index⟩ ⦃ answer =>
      answer.1 = .Ok (view (store.memories.val[index.val]).buf) ∧
      ∀ bytes : Slice U8, bytes.length = (view (store.memories.val[index.val]).buf).length →
        CertifiedApiStore emission allowed view code (answer.2 (.Ok bytes)) ∧
        Store.FunctionCapacities code (answer.2 (.Ok bytes)) ∧
        Extend_store (Store.decodeStore view code store)
          (Store.decodeStore view code (answer.2 (.Ok bytes))) ⦄ := by
  unfold runtime.store.Store.memory_mut
  simp
  step as ⟨m, vecBack, found, backward⟩
  obtain ⟨back, read, write⟩ := laws.write m.buf
  rw [read]
  simp
  constructor
  · simp [found]
  · intro bytes sameLength
    subst vecBack
    have bytesView : view (back bytes) = bytes := write bytes (by simpa [found] using sameLength)
    let after := {store with memories := store.memories.set index {m with buf := back bytes}}
    have shape : Store.Shape view after := by
      apply certified.shape.memory_replace_same_length index inBounds
      · simpa [bytesView] using sameLength
      · simp [found]
    have sourceSyntax : Store.StoreSyntax code after := certified.storeSyntax
    have oldWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
    have newWf := Store.decodeStore_wf view code after shape sourceSyntax
    have oldMemoryWf : wf_meminst (Store.decodeMemory view m) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply Store.decodeLimits_wf
        have bound := (certified.shape.memories m (by simp [found])).2.1
        scalar_tac
      · exact Store.decodeBytes_wf _
    have newMemoryWf : wf_meminst (Store.decodeMemory view {m with buf := back bytes}) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply Store.decodeLimits_wf
        have bound := (certified.shape.memories m (by simp [found])).2.1
        simp only [bytesView, sameLength]
        simp only [found] at bound
        scalar_tac
      · exact Store.decodeBytes_wf _
    have objectExtension := Store.decodeMemory_extends view m {m with buf := back bytes}
      rfl (by simpa [bytesView, found] using Nat.le_of_eq sameLength.symm) oldMemoryWf newMemoryWf
    have extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after) := by
      unfold after at newWf ⊢
      rw [Store.decodeStore_memory_update view code store
        (store.memories.set index {m with buf := back bytes})] at newWf ⊢
      simp only [alloc.vec.Vec.set_val_eq, List.map_set] at newWf ⊢
      apply Spec.extend_store_set_mem _ _ _ oldWf
      · simpa only [Store.decodeStore] using newWf
      · intro bound
        simpa only [Store.decodeStore, found,
          getElem!_pos (store.memories.val.map (Store.decodeMemory view)) index.val
            (by simpa only [List.length_map] using inBounds), List.getElem_map] using objectExtension
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩
end Exec.Theorems.CertifiedApi
