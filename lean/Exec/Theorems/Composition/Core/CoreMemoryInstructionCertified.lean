import Exec.Interp.Memory.MemoryMutation
import Exec.Theorems.Composition.Certified.CertifiedCoreContent
import Exec.Store.Invariant.ObjectExtension

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt
open Exec.Store Exec.Interp

/-- A byte-length-preserving instruction update retains the current executable
store certificate. -/
theorem memory_mutation_core_certified {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedCoreStore view code before)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (issued : before.memories.val[address.index.val]? = some object)
    (mutation : Interp.MemoryMutation view before after address object) :
    CertifiedCoreStore view code after ∧
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
theorem memory_store_core_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M) (addressWord valueWord : U64)
    (ambient : frame) (argument : memarg)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val + value.val]? = some valueWord)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store)
    (ambientWf : wf_frame ambient)
    (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_store memory exec store instanceIndex base (MemoryDescriptor.storeOpcode op) address value offset ⦃ out => MemoryMutation view store out.2 memoryAddress object ∧ FrameStoreMetadata store out.2 ∧
      CertifiedCoreStore view code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,
          .CONST op.type (numericStoreValue op.type valueWord),admininstr_instr (op.source argument)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → decodeStore view code out.2 = decodeStore view code store) ⦄ := by
  have storeWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  apply WP.spec_mono (MemoryDescriptor.execute_store_core memory view laws code exec store instanceIndex base op address value offset
    inst memoryAddress object addressWord valueWord ambient argument found mapped issued input inputValue
    moduleEq storeWf ambientWf operationWf offsetEq)
  intro out effect
  obtain ⟨mutation,metadata,source⟩ := effect
  have preserved := memory_mutation_core_certified view code store out.2 certified memoryAddress object issued mutation
  exact ⟨mutation,metadata,preserved.1,preserved.2,source⟩
end Exec.Theorems
