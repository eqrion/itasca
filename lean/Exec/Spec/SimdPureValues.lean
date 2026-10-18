import Exec.Spec.SimdShape
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

/-- Source values represented by SIMD operand bits. SIMD uses only numerical
and vector types; reference cases retain a total definition. -/
def valueOfBits (ty : valtype) (bits : BitVec 128) : val :=
  match ty with
  | .I32 => .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat))
  | .I64 => .CONST .I64 (.mk_num__0 .I64 (.mk_uN (bits.setWidth 64).toNat))
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (bits.setWidth 32).toNat))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 (bits.setWidth 64).toNat))
  | .V128 => .VCONST .V128 (.mk_uN bits.toNat)
  | .FUNCREF => .REF_NULL .FUNCREF
  | .EXTERNREF => .REF_NULL .EXTERNREF
  | .BOT => .REF_NULL .FUNCREF

/-- Up to three SIMD operands in their source order. -/
def operandValues (types : List valtype) (x y z : BitVec 128) : List val :=
  List.zipWith valueOfBits types [x,y,z]

theorem valueOfBits_wf (ty : valtype) (bits : BitVec 128) : wf_val (valueOfBits ty bits) := by
  cases ty
  · exact .val_case_0 _ _ (unsigned_num_wf .I32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))
  · exact .val_case_0 _ _ (unsigned_num_wf .I64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))
  · exact .val_case_0 _ _ (float_num_wf .F32 _ (floatOfBits_wf_32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))))
  · exact .val_case_0 _ _ (float_num_wf .F64 _ (floatOfBits_wf_64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))))
  · exact .val_case_1 _ _ (by decide) (unsigned_wf_of_lt 128 _ bits.isLt)
  · exact .val_case_2 _
  · exact .val_case_2 _
  · exact .val_case_2 _

theorem operandValues_wf (types : List valtype) (x y z : BitVec 128) :
    Forall wf_val (operandValues types x y z) := by
  have all (types : List valtype) (words : List (BitVec 128)) :
      Forall wf_val (List.zipWith valueOfBits types words) := by
    induction types generalizing words with
    | nil => simp [Forall]
    | cons ty types ih =>
      cases words with
      | nil => simp [Forall]
      | cons word words =>
        intro value member
        simp only [List.zipWith_cons_cons,List.mem_cons] at member
        rcases member with rfl | member
        · exact valueOfBits_wf ty word
        · exact ih words value member
  exact all types [x,y,z]

theorem operandValues_length (types : List valtype) (x y z : BitVec 128)
    (arity : types.length ≤ 3) : (operandValues types x y z).length = types.length := by
  simp only [operandValues,List.length_zipWith,List.length_cons,List.length_nil]
  exact Nat.min_eq_left arity
end Exec.Spec.Simd
