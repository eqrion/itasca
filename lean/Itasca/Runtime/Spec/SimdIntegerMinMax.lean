import Itasca.Runtime.Spec.SimdCompareLists
import Itasca.Runtime.Spec.IntegerSigned
namespace Itasca.Runtime.Spec.Simd

inductive IntegerMinMax where | minS | minU | maxS | maxU

def integerMinMaxBits (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with
  | .minS => if a.toInt < b.toInt then a else b
  | .minU => if a.toNat < b.toNat then a else b
  | .maxS => if a.toInt > b.toInt then a else b
  | .maxU => if a.toNat > b.toNat then a else b

def IntegerMinMaxRel (kind : IntegerMinMax) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .minS => fun_imin_ width .S a b result
  | .minU => fun_imin_ width .U a b result
  | .maxS => fun_imax_ width .S a b result
  | .maxU => fun_imax_ width .U a b result

theorem integer_minmax_relation (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) :
    IntegerMinMaxRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerMinMaxBits kind a b).toNat) := by
  cases kind with
  | minU =>
    by_cases h : a.toNat < b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imin_.fun_imin__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | maxU =>
    by_cases h : a.toNat > b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imax_.fun_imax__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | minS =>
    have source := fun_imin_.fun_imin__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt < b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≤ b.toInt by omega] using source
  | maxS =>
    have source := fun_imax_.fun_imax__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt > b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≥ b.toInt by omega] using source

end Itasca.Runtime.Spec.Simd
