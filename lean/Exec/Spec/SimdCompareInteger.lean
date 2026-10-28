import Exec.Spec.IntegerSigned
namespace Itasca.Runtime.Spec.Simd

def integerLaneCompare {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) : Bool :=
  match op with
  | .EQ => decide (a.toNat = b.toNat)
  | .NE => decide (a.toNat ≠ b.toNat)
  | .LT .U => decide (a.toNat < b.toNat)
  | .GT .U => decide (a.toNat > b.toNat)
  | .LE .U => decide (a.toNat ≤ b.toNat)
  | .GE .U => decide (a.toNat ≥ b.toNat)
  | .LT .S => decide (a.toInt < b.toInt)
  | .GT .S => decide (a.toInt > b.toInt)
  | .LE .S => decide (a.toInt ≤ b.toInt)
  | .GE .S => decide (a.toInt ≥ b.toInt)

def IntegerLaneRel (op : vrelop_Jnn_N) (width : Nat) (a b answer : uN) : Prop :=
  match op with
  | .EQ => fun_ieq_ width a b answer
  | .NE => fun_ine_ width a b answer
  | .LT sign => fun_ilt_ width sign a b answer
  | .GT sign => fun_igt_ width sign a b answer
  | .LE sign => fun_ile_ width sign a b answer
  | .GE sign => fun_ige_ width sign a b answer

theorem integer_lane_compare_relation {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) :
    IntegerLaneRel op width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (nat_of_bool (integerLaneCompare op a b))) := by
  cases op with
  | EQ => exact .fun_ieq__case_0 _ _ _ (boolean_u32_wf _)
  | NE =>
    have boolean : (uN.mk_uN a.toNat != uN.mk_uN b.toNat) = decide (a.toNat ≠ b.toNat) := by
      change (a.toNat != b.toNat) = _
      by_cases same : a.toNat = b.toNat
      · simp [same]
      · have different := beq_eq_false_iff_ne.mpr same
        simp [bne,different,same]
    have relation := fun_ine_.fun_ine__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (boolean_u32_wf _)
    rw [boolean] at relation
    exact relation
  | LT sign => cases sign with
    | U => exact .fun_ilt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ilt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GT sign => cases sign with
    | U => exact .fun_igt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_igt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | LE sign => cases sign with
    | U => exact .fun_ile__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ile__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GE sign => cases sign with
    | U => exact .fun_ige__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ige__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)

end Itasca.Runtime.Spec.Simd
