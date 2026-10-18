import Exec.Interp.Relations.PackedMemoryDispatch
import Exec.Abs.Memory.Descriptor

namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt
open Exec.Store

/-- The abstract indexed widths and the independent source helper enumerate the
same legal packed instructions. No execution relation is assumed by this map. -/
def packed {ty : Inn} (width : Abs.Memory.PackedWidth ty) : Spec.PackedMemory :=
  match ty,width with
  | .I32,.byte => .i32x8
  | .I32,.half => .i32x16
  | .I64,.byte => .i64x8
  | .I64,.half => .i64x16
  | .I64,.word => .i64x32

theorem packed_type {ty : Inn} (width : Abs.Memory.PackedWidth ty) : (packed width).type = ty := by
  cases ty <;> cases width <;> rfl

theorem packed_bytes {ty : Inn} (width : Abs.Memory.PackedWidth ty) :
    (packed width).bytes = width.bits / 8 := by cases ty <;> cases width <;> rfl

theorem packed_load {ty : Inn} (width : Abs.Memory.PackedWidth ty) (sign : sx) (arg : memarg) :
    (packed width).load sign arg = admininstr_instr (Abs.Memory.Load.packed ty width sign |>.source arg) := by
  cases ty <;> cases width <;> rfl

theorem packed_store {ty : Inn} (width : Abs.Memory.PackedWidth ty) (arg : memarg) :
    (packed width).store arg = admininstr_instr (Abs.Memory.Store.packed ty width |>.source arg) := by
  cases ty <;> cases width <;> rfl

def loadOpcode : Abs.Memory.Load → U16
  | .full ty => numericLoadOpcode ty
  | .packed _ width sign => PackedMemory.loadOpcode (packed width) sign

def storeOpcode : Abs.Memory.Store → U16
  | .full ty => numericStoreOpcode ty
  | .packed _ width => PackedMemory.storeOpcode (packed width)

theorem load_width (op : Abs.Memory.Load) : (scalarLoadWidth (loadOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width sign => exact (PackedMemory.load_width _ _).trans (packed_bytes width)

theorem store_width (op : Abs.Memory.Store) : (scalarStoreWidth (storeOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width => exact (PackedMemory.store_width _).trans (packed_bytes width)
theorem execute_store_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
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
    runtime.interp.execute_store memory exec store instanceIndex base (storeOpcode op) address value offset ⦃ out =>
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,
          .CONST op.type (numericStoreValue op.type valueWord),admininstr_instr (op.source argument)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → decodeStore view code out.2 = decodeStore view code store) ⦄ := by
  cases op with
  | full ty =>
    apply WP.spec_mono (Interp.execute_numeric_store_source memory view laws code exec store instanceIndex base ty address value offset inst
        memoryAddress object addressWord valueWord ambient argument found mapped issued input inputValue
        moduleEq storeWf ambientWf operationWf offsetEq)
    rintro ⟨result,after⟩ effect
    cases result <;> simpa only [storeOpcode,Abs.Memory.Store.source,Abs.Memory.Store.type,
      Abs.Memory.Store.operation,admininstr_instr] using effect
  | packed ty width =>
    apply WP.spec_mono (PackedMemory.execute_store_source memory view laws code exec store instanceIndex base (packed width) address value offset inst
        memoryAddress object addressWord valueWord ambient argument found mapped issued input inputValue
        moduleEq storeWf ambientWf (by simpa only [packed_store] using operationWf) offsetEq)
    rintro ⟨result,after⟩ effect
    cases result <;> simpa only [storeOpcode,Abs.Memory.Store.type,packed_type,packed_store] using effect


theorem execute_load_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Load) (dst address offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M) (addressWord : U64)
    (ambient : frame) (argument : memarg)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (capacity : base.val + dst.val < exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_load memory exec store instanceIndex base (loadOpcode op) dst address offset ⦃ out =>
      (∃ word, out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) word) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,admininstr_instr (op.source argument)]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[admininstr_val (decodeWords (numericMemoryType op.type) word 0#u64)]⟩) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 addressWord).val,admininstr_instr (op.source argument)]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[.TRAP]⟩) ⦄ := by
  cases op with
  | full ty =>
    simpa only [loadOpcode,Abs.Memory.Load.source,Abs.Memory.Load.type,
      Abs.Memory.Load.operation,admininstr_instr] using
      Interp.execute_numeric_load_source memory view laws code exec store instanceIndex base ty dst address offset inst
        memoryAddress object addressWord ambient argument found mapped issued input capacity
        moduleEq storeWf ambientWf operationWf offsetEq
  | packed ty width sign =>
    simpa only [loadOpcode,Abs.Memory.Load.type,packed_type,packed_load] using
      PackedMemory.execute_load_source memory view laws code exec store instanceIndex base (packed width) sign dst address offset inst
        memoryAddress object addressWord ambient argument found mapped issued input capacity
        moduleEq storeWf ambientWf (by simpa only [packed_load] using operationWf) offsetEq

end Exec.Interp.MemoryDescriptor
