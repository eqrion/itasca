import Itasca.Runtime.Interp.Simd.Integer.Saturation
import Itasca.Runtime.Spec.Simd.Q15

/-!
Word-level rounded saturating Q15 multiplication.

Main declarations: `q15Word`. A direct consumer is `Interp.Simd.Integer.Dot`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def q15Word (a b : I64) : Result U64 :=
  Aeneas.Std.bind (Aeneas.Std.bind (Aeneas.Std.bind (Aeneas.Std.bind (a * b)
    (fun product => product + 16384#i64))
    (fun rounded => rounded >>> 15#i32))
    (fun shifted => lift (IScalar.cast .I128 shifted)))
    (fun widened => runtime.interp.simd.sat widened 16#u32 true)

@[step] theorem q15_word (a b : I64)
    (aBound : -32768 ≤ a.val ∧ a.val < 32768)
    (bBound : -32768 ≤ b.val ∧ b.val < 32768) :
    q15Word a b ⦃ result => result.bv.setWidth 16 =
      BitVec.ofInt 16 (clampLane 16 true ((a.val*b.val+16384)/32768)) ⦄ := by
  have p1 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ b.val+32768)
  have p2 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ 32768-b.val)
  have p3 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ 32768-b.val)
  have p4 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ b.val+32768)
  have productBound : -1073741824 ≤ a.val*b.val ∧ a.val*b.val ≤ 1073741824 := by constructor <;> nlinarith
  unfold q15Word
  simp only [Std.bind_assoc]
  step* <;> simp_all [Int.shiftRight_eq_div_pow] <;> first | (with_unfolding_all assumption) | scalar_tac

end Itasca.Runtime.Interp.Simd
