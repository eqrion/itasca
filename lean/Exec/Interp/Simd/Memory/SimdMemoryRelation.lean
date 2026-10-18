import Exec.Interp.Simd.Memory.SimdMemoryLoadSource
import Exec.Interp.Simd.Memory.SimdMemoryStoreSource
import Exec.Interp.Simd.Memory.SimdMemoryZeroSource
import Exec.Interp.Simd.Memory.SimdMemoryLaneSource
import Exec.Interp.Simd.Memory.SimdMemoryLaneStoreSource
import Exec.Interp.Simd.Memory.SimdMemorySplatSource
import Exec.Interp.Simd.Memory.SimdMemoryExtendSource
import Exec.Interp.Simd.Memory.SimdMemoryDispatch
import Exec.Spec.SimdPureValues
import Exec.Code.Local.Lowering.Simd.SimdSourceShape
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

/-- Exact buffer changes permitted by a vector memory instruction. The write constructor retains
    both its bounded payload and the corresponding source-store update. -/
inductive MemoryBufferChange (s : store) (f : frame) (before : Slice U8) : Slice U8 → store → Prop
  | unchanged : MemoryBufferChange s f before before s
  | write (start : Nat) (payload : List byte) (after : Slice U8)
      (inside : start + payload.length ≤ before.length)
      (payloadWf : Forall wf_byte payload)
      (written : Store.decodeBytes after.val = (Store.decodeBytes before.val).setSlice! start payload) :
      MemoryBufferChange s f before after (Spec.memoryPayloadWrite s f start payload)

theorem MemoryBufferChange.length {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : after.length = before.length := by
  cases change with
  | unchanged => rfl
  | write start payload after inside payloadWf written =>
    simpa only [Store.decodeBytes,List.length_map,List.length_setSlice!,Slice.length] using congrArg List.length written

def memorySourceInput (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (x y z : BitVec 128) : List admininstr :=
  (Spec.Simd.operandValues op.inputs x y z).map admininstr_val ++
    [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]

def MemorySourceEffect (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (x y z : BitVec 128) (s : store) (f : frame) (before : Slice U8)
    (status : core.result.Result U128 runtime.ExecError) (after : Slice U8) : Prop :=
  match status with
  | .Ok value => ∃ sourceAfter, MemoryBufferChange s f before after sourceAfter ∧
      StepH ⟨⟨s,f⟩,memorySourceInput op argument laneIndex x y z⟩ []
        ⟨⟨sourceAfter,f⟩,(Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩
  | .Err error => error = .Trap .MemoryOutOfBounds ∧ after = before ∧
      StepH ⟨⟨s,f⟩,memorySourceInput op argument laneIndex x y z⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩

def MemoryOperationSound (opcode : U32) : Prop :=
  ∀ op, memoryMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (x y z : U128) (bytes : Slice U8) (s : store) (f : frame) (argument : memarg),
    wf_store s → wf_frame f → wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN laneIndex.val))) →
    proj_uN_0 argument.OFFSET = offset.val →
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.memory_op opcode offset laneIndex x y bytes
      ⦃ result => MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 result.2 ⦄

theorem memory_input_scalar (x : U128) :
    admininstr_val (Spec.Simd.valueOfBits .I32 x.bv) = Spec.Segment.i32 (UScalar.cast .U32 x).val := by
  rfl
end Exec.Interp.Simd
