import Exec.Interp.Memory.MemoryMutation
import Exec.Store.Api.MemoryCopyEffect
namespace Exec.Store
open Aeneas Aeneas.Std Exec.Interp

theorem MemoryCopyEffect.mutation {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryCopyEffect view store address.index memory destination source count out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ MemoryMutation view store out.2 address memory) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ out.2 = store)) := by
  unfold MemoryCopyEffect at effect
  split at effect
  · obtain ⟨buffer,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,buffer,rfl,?_⟩⟩
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Exec.Store
