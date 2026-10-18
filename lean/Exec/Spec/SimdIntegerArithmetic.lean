import Exec.Spec.SimdCompareLists
namespace Exec.Spec.Simd

inductive IntegerArithmetic where | add | sub | mul

def integerArithmeticBits (kind : IntegerArithmetic) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with | .add => a+b | .sub => a-b | .mul => a*b

def IntegerArithmeticRel (kind : IntegerArithmetic) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .add => fun_iadd_ width a b result
  | .sub => fun_isub_ width a b result
  | .mul => fun_imul_ width a b result

theorem integer_arithmetic_relation (kind : IntegerArithmetic) {width : Nat} (a b : BitVec width) :
    IntegerArithmeticRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerArithmeticBits kind a b).toNat) := by
  have wf := unsigned_wf_of_lt width (integerArithmeticBits kind a b).toNat (BitVec.isLt _)
  cases kind with
  | add =>
    simpa only [IntegerArithmeticRel,integerArithmeticBits,BitVec.toNat_add,proj_uN_0] using
      fun_iadd_.fun_iadd__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simpa only [integerArithmeticBits,BitVec.toNat_add,proj_uN_0] using wf)
  | mul =>
    simpa only [IntegerArithmeticRel,integerArithmeticBits,BitVec.toNat_mul,proj_uN_0] using
      fun_imul_.fun_imul__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simpa only [integerArithmeticBits,BitVec.toNat_mul,proj_uN_0] using wf)
  | sub =>
    have formula : (a-b).toNat = ((2^width+(a.toNat:Int)-b.toNat)%(2^width:Int)).toNat := by
      rw [BitVec.toNat_sub]
      have castEq : (((2^width-b.toNat+a.toNat)%2^width : Nat) : Int) =
          (2^width+(a.toNat:Int)-b.toNat)%(2^width:Int) := by
        rw [Int.natCast_emod,Nat.cast_add,Nat.cast_sub (Nat.le_of_lt b.isLt),Nat.cast_pow,Nat.cast_ofNat]
        congr 1
        omega
      exact congrArg Int.toNat castEq
    have relation := fun_isub_.fun_isub__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (by simpa only [integerArithmeticBits,formula,proj_uN_0] using wf)
    simpa only [IntegerArithmeticRel,integerArithmeticBits,formula,proj_uN_0] using relation

end Exec.Spec.Simd
