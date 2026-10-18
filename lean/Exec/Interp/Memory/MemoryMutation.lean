import Exec.Interp.Memory.MemoryDescriptor
import Exec.Interp.Relations.FrameStoreMetadata

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
open Exec.Store

/-- A scalar memory instruction changes only the selected opaque buffer and
retains its byte length. This includes bounds failures whose writeback callback
chooses a different representation of the same bytes. -/
def MemoryMutation {M : Type} (view : M → Slice U8) (before after : runtime.store.Store M)
    (address : runtime.MemoryAddr) (object : runtime.store.Memory M) : Prop :=
  ∃ buffer, after = {before with memories := before.memories.set address.index {object with buf := buffer}} ∧
    (view buffer).length = (view object.buf).length

theorem MemoryMutation.frame_metadata {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {address object}
    (mutation : MemoryMutation view before after address object) : FrameStoreMetadata before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem execute_store_mutation {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (opcode : U16) (address value offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord valueWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val + value.val]? = some valueWord) :
    runtime.interp.execute_store memory exec store instanceIndex base opcode address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧ FrameStoreMetadata store out.2 ⦄ := by
  apply WP.spec_mono (execute_store_effect memory view laws exec store instanceIndex base opcode address value offset
    inst memoryAddress object addressWord valueWord found mapped issued input inputValue)
  intro out effect
  obtain ⟨buffer,after,effect⟩ := effect
  have lengthEq : (view buffer).length = (view object.buf).length := by
    unfold ScalarStoreEffect at effect
    split at effect
    · obtain ⟨_,bytesEq⟩ := effect
      change (view buffer).val.length = (view object.buf).val.length
      rw [bytesEq,scalarStoreBytes_length]
    · have same : view buffer = view object.buf := congrArg Prod.snd effect
      rw [same]
  have mutation : MemoryMutation view store out.2 memoryAddress object := ⟨buffer,after,lengthEq⟩
  exact ⟨mutation,mutation.frame_metadata⟩

theorem MemoryDescriptor.execute_store_core {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord valueWord : U64)
    (ambient : frame) (argument : memarg)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val + value.val]? = some valueWord)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_store memory exec store instanceIndex base (MemoryDescriptor.storeOpcode op) address value offset ⦃ out => MemoryMutation view store out.2 memoryAddress object ∧ FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,
          .CONST op.type (numericStoreValue op.type valueWord),admininstr_instr (op.source argument)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → decodeStore view code out.2 = decodeStore view code store) ⦄ := by
  have mutation := execute_store_mutation memory view laws exec store instanceIndex base
    (MemoryDescriptor.storeOpcode op) address value offset inst memoryAddress object addressWord valueWord
    found mapped issued input inputValue
  obtain ⟨out,run,effect⟩ := WP.spec_imp_exists mutation
  have source := MemoryDescriptor.execute_store_source memory view laws code exec store instanceIndex base op address value offset
    inst memoryAddress object addressWord valueWord ambient argument found mapped issued input inputValue
    moduleEq storeWf ambientWf operationWf offsetEq
  rw [run,WP.spec_ok] at source ⊢
  exact ⟨effect.1,effect.2,source⟩
end Exec.Interp
