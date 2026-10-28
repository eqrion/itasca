import Itasca.Runtime.Interp.Simd.Common.SimdValueSlots
import Itasca.Runtime.Interp.Simd.Common.SimdPureRelation
import Itasca.Runtime.Spec.PureWf
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdSourceShape
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

theorem ValuesAt.simd_pure_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (signature : Signature) (value : U128)
    (before : List admininstr)
    (source : Step_pure before [admininstr_val (Simd.pureResult signature value.bv)])
    (capacity : base + Code.slots (front.map Code.valueType) +
      (Code.simdSourceWidth signature.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Code.slots (front.map Code.valueType))
      (Code.simdSourceWidth signature.outputs[0]?) value) base
      (front ++ [Simd.pureResult signature value.bv]) := by
  cases signature
  all_goals try exact represented.simd_vector_result value capacity
  have bound : value.val < 2^32 := Spec.pure_i32_bound source
  have cast : (UScalar.cast .U64 value).val = value.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have result := represented.simd_scalar_result .I32 value (by intro h; cases h)
    (by intro _; rw [cast]; exact bound) (by change base + Code.slots _ + 1 ≤ words.length at capacity; omega)
  have decoded : Store.decodeWords .I32 (UScalar.cast .U64 value) 0#u64 =
      Simd.pureResult .test value.bv := by
    change val.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((UScalar.cast .U64 value).val % 2^32))) = _
    rw [cast,Nat.mod_eq_of_lt bound]
    rfl
  rw [decoded] at result
  exact result
end Itasca.Runtime.Interp
