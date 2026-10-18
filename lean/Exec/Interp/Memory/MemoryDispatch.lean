import Exec.Interp.Memory.MemoryScalar
import Exec.Interp.Relations.Fetch
import Exec.Platform.Memory

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Loads trap before modifying execution slots, and successful loads write only
the designated result slot. Memory access is through the explicit dictionary law. -/
theorem execute_load_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (opcode : U16) (dst address offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (capacity : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_load memory exec store instanceIndex base opcode dst address offset ⦃ out =>
      if (UScalar.cast .U32 addressWord).val + offset.val + (scalarLoadWidth opcode).val ≤ (view object.buf).length then
        out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val + dst.val)
          (scalarLoadedWord opcode (scalarLoadBytes (view object.buf).val
            ((UScalar.cast .U32 addressWord).val + offset.val) 0#u64 0 (scalarLoadWidth opcode).val)))
      else out = (.Err (.Trap .MemoryOutOfBounds),exec) ⦄ := by
  have inputBound : base.val + address.val < exec.slots.length := (List.getElem?_eq_some_iff.mp input).1
  unfold runtime.interp.execute_load
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize memoryAddress (by simpa using mapped) as ⟨actual,actualEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  step with vec_index_given exec.slots position addressWord (by simpa only [positionEq,U32.cast_Usize_val_eq] using input) as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given store.memories memoryAddress.index object issued as ⟨actual,actualEq⟩
  subst actual
  rw [laws.read,bind_ok]
  step with memory_load_effect opcode (UScalar.cast .U32 addressWord) offset (view object.buf) as ⟨result,effect⟩
  unfold ScalarLoadEffect at effect
  split at effect
  · rename_i fits
    rw [effect]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,lift,if_pos fits]
    step as ⟨destination,destinationEq⟩
    step as ⟨old,back,oldEq,backEq⟩
    simp [SlotsEffect,backEq,destinationEq]
  · rename_i outside
    rw [effect]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,outside]
    scalar_tac

/-- The complete store dispatch retains every object except the selected memory
buffer. Even on a bounds trap, the callback's opaque representation may change;
its decoded bytes remain exactly unchanged. -/
theorem execute_store_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
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
      ∃ buffer, out.2 = {store with memories := store.memories.set memoryAddress.index {object with buf := buffer}} ∧
        ScalarStoreEffect opcode (UScalar.cast .U32 addressWord) offset valueWord (view object.buf) (out.1,view buffer) ⦄ := by
  have inputBound : base.val + address.val < exec.slots.length := (List.getElem?_eq_some_iff.mp input).1
  have valueBound : base.val + value.val < exec.slots.length := (List.getElem?_eq_some_iff.mp inputValue).1
  unfold runtime.interp.execute_store
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize memoryAddress (by simpa using mapped) as ⟨actual,actualEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  step with vec_index_given exec.slots position addressWord (by simpa only [positionEq,U32.cast_Usize_val_eq] using input) as ⟨actual,actualEq⟩
  subst actual
  step as ⟨valuePosition,valuePositionEq⟩
  step with vec_index_given exec.slots valuePosition valueWord (by simpa only [valuePositionEq,U32.cast_Usize_val_eq] using inputValue) as ⟨actual,actualEq⟩
  subst actual
  have objectBound : memoryAddress.index.val < store.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  step as ⟨old,back,oldEq,backEq⟩
  have oldSame : old = object := by
    have atIndex := List.getElem?_eq_getElem objectBound
    rw [issued] at atIndex
    exact oldEq.trans (Option.some.inj atIndex).symm
  subst old
  rw [oldSame]
  obtain ⟨writeBack,writeEq,writeLaw⟩ := laws.write object.buf
  rw [writeEq,bind_ok]
  step with memory_store_effect opcode (UScalar.cast .U32 addressWord) offset valueWord (view object.buf) as ⟨status,written,effect⟩
  have lengthEq : written.length = (view object.buf).length := by
    unfold ScalarStoreEffect at effect
    split at effect
    · obtain ⟨_,bytesEq⟩ := effect
      change written.val.length = (view object.buf).val.length
      rw [bytesEq,scalarStoreBytes_length]
    · have same := congrArg Prod.snd effect
      simpa using congrArg Slice.length same
  have restored := writeLaw written lengthEq
  refine ⟨writeBack written,?_,?_⟩
  · simp [backEq]
  · simpa only [restored] using effect
end Exec.Interp
