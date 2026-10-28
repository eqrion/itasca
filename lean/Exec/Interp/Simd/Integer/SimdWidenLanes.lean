import Exec.Interp.Simd.Integer.SimdWidenWord
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def widenWidth (ty : WidenWidth) : U32 := match ty with
  | .i8 => 8#u32 | .i16 => 16#u32 | .i32 => 32#u32

def widenOpcode (ty : WidenWidth) (multiply high signed : Bool) : U32 :=
  ⟨BitVec.ofNat 32 ((match ty with | .i8 => 128 | .i16 => 160 | .i32 => 192) +
    (if multiply then 28 else 7) + (if signed then 0 else 2) + (if high then 1 else 0))⟩

theorem widenWidth_val (ty : WidenWidth) : (widenWidth ty).val = ty.width := by cases ty <;> rfl

theorem widen_dispatch_eq (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y =
      (runtime.interp.simd.widen_lanes_loop x (widenWidth ty) multiply high
        signed (if multiply then y else 0#u128) 0#u128 0#u32) := by
  cases ty <;> cases multiply <;> cases high <;> cases signed
  all_goals unfold runtime.interp.simd.widen_lanes widenOpcode widenWidth
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _; rw [bind_ok])
  all_goals with_unfolding_all rfl

@[step] theorem widen_lanes (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y ⦃ result =>
      ∀ j, j < ty.count → laneBits (ty.width*2) j result.bv = widenBits multiply signed
        (laneBits ty.width (j+if high then ty.count else 0) x.bv)
        (laneBits ty.width (j+if high then ty.count else 0) y.bv) ⦄ := by
  rw [widen_dispatch_eq]
  have widthEq := widenWidth_val ty
  have loopLaw := widen_loop (widenWidth ty) 0#u32 multiply high signed x (if multiply then y else 0#u128) 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = widenBits multiply signed
      (laneBits (widenWidth ty).val (j+if high then 64/(widenWidth ty).val else 0) x.bv)
      (laneBits (widenWidth ty).val (j+if high then 64/(widenWidth ty).val else 0) (if multiply then y else 0#u128).bv))
    (by intro j valid a b aEq bEq; exact widen_word _ _ _ _ _ _ _ (by cases ty <;> decide) (by cases ty <;> decide) aEq bEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro out lanes j valid
  rw [widthEq] at lanes
  have result := lanes j valid
  cases multiply <;> simpa only [Bool.false_eq_true,Bool.true_eq,↓reduceIte,widenBits,WidenWidth.count] using result
end Itasca.Runtime.Interp.Simd
