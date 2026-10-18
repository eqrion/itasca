import Exec.Interp.Simd.Common.SimdPureRelation
import Exec.Interp.Simd.Common.SimdExtractSound
import Exec.Interp.Simd.Integer.SimdExtractSignedSound
import Exec.Interp.Simd.Common.SimdReplaceSound
import Exec.Spec.PureWf
import Exec.Spec.ByteEncoding
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def laneResult (op : LaneOperation) (bits : BitVec 128) : val :=
  Spec.Simd.valueOfBits (if op.replace then .V128 else valtype_numtype op.scalar) bits

def LaneSourceEffect (op : LaneOperation) (laneIndex : Nat) (x y z value : BitVec 128) : Prop :=
  Step_pure ((Spec.Simd.operandValues op.inputs x y z).map admininstr_val ++
    [admininstr_instr (op.instruction (.mk_uN laneIndex))]) [admininstr_val (laneResult op value)]

def LaneResultBound (op : LaneOperation) (value : U128) : Prop :=
  op.replace = false → value.val < 2^(Spec.scalarNumBytes op.scalar*8)

def LaneEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op : LaneOperation, laneMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)),
    laneIndex.val < op.count →
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧ LaneSourceEffect op laneIndex.val x.bv y.bv z.bv value.bv ∧ LaneResultBound op value ⦄

theorem extract_result_value (ty : lanetype) (value : U128) (bounded : value.val < 2^lsize ty) :
    admininstr_val (Spec.Simd.valueOfBits (valtype_numtype (unpack ty)) value.bv) =
      .CONST (unpack ty) (Spec.Simd.scalarOutput ty value.val) := by
  have narrow (n : Nat) (le : lsize ty ≤ n) : (value.bv.setWidth n).toNat = value.val := by
    rw [BitVec.toNat_setWidth,UScalar.bv_toNat,Nat.mod_eq_of_lt (lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide) le))]
  cases ty <;> simp only [Spec.Simd.valueOfBits,Spec.Simd.scalarOutput,unpack,valtype_numtype,admininstr_val]
  all_goals rw [narrow _ (by decide)]

@[step] theorem extract_dispatch_values {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8))
    (valid : laneIndex.val < 128/lsize ty) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf ty) (Spec.Simd.extractSign ty) (.mk_uN laneIndex.val)]
          [admininstr_val (Spec.Simd.valueOfBits (valtype_numtype (unpack ty)) value.bv)] ∧ value.val < 2^(Spec.scalarNumBytes (unpack ty)*8) ⦄ := by
  rw [extract_dispatch_eq]
  step with extract_access ty laneIndex x y valid as ⟨result,value,returned,valueEq⟩
  refine ⟨value,by rw [returned],?_,?_⟩
  · rw [extract_result_value ty value (by rw [valueEq];exact Nat.mod_lt _ (by positivity)),valueEq]
    exact Spec.Simd.extract_step ty laneIndex.val x.bv valid
  · rw [valueEq]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by decide) (by cases ty <;> decide))
end Exec.Interp.Simd
