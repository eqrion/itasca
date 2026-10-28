import Exec.Abs.Float.Progress
import Exec.Interp.Numeric.Float.FloatBounded
import Exec.Interp.Numeric.Float.FloatSource
import Exec.Interp.Numeric.Float.FloatMinMaxSource
import Exec.Interp.Numeric.Float.FloatComparisonScalar
import Exec.Spec.FloatComparison
import Exec.Interp.Numeric.Float.FloatConvertSource
import Exec.Interp.Numeric.Float.FloatPromoteSource
import Exec.Interp.Numeric.Float.FloatReinterpretSource
import Exec.Interp.Numeric.Float.FloatTruncSource
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

def floatOpcode (op : Abs.Float.Instruction) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

def floatInput (ty : numtype) (value : U64) : Nat :=
  match ty with
  | .I32 | .F32 => (UScalar.cast .U32 value).val
  | .I64 | .F64 => value.val

def FloatScalarOutcome (op : Abs.Float.Instruction) (a b : U64)
    (result : core.result.Result U64 runtime.ExecError) : Prop :=
  match result with
  | .Ok value => op.Result (floatInput op.input a) (floatInput op.input b) (some value.val)
  | .Err (.Trap reason) => op.Result (floatInput op.input a) (floatInput op.input b) none ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem spec_both {α : Type} {computation : Result α} {P Q : α → Prop}
    (first : WP.spec computation P) (second : WP.spec computation Q) :
    WP.spec computation (fun result => P result ∧ Q result) := by
  cases first with
  | ret first => exact WP.spec.ret ⟨first, (WP.spec_ok _).mp second⟩

theorem signed_roundtrip32 (a : U64) : (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val = (UScalar.cast .U32 a).val := by
  with_unfolding_all change ((a.bv.setWidth 32).signExtend 32).toNat = (a.bv.setWidth 32).toNat
  rw [BitVec.signExtend_eq]

theorem signed_roundtrip64 (a : U64) : (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val = a.val := by
  with_unfolding_all change ((a.bv.setWidth 64).signExtend 64).toNat = a.bv.toNat
  rw [BitVec.signExtend_eq, BitVec.setWidth_eq]

end Itasca.Runtime.Interp
