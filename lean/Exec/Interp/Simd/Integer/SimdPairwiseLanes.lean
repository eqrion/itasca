import Exec.Interp.Simd.Integer.SimdPairwiseWord
import Exec.Interp.Simd.Integer.SimdWidenLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def pairwiseOpcode (ty : PairwiseWidth) (signed : Bool) : U32 :=
  match ty,signed with | .i8,true => 124#u32 | .i8,false => 125#u32 | .i16,true => 126#u32 | .i16,false => 127#u32

theorem pairwise_dispatch_eq (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x =
      (runtime.interp.simd.pairwise_add_lanes_loop x (widenWidth ty.widen) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.pairwise_add_lanes pairwiseOpcode widenWidth PairwiseWidth.widen
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_lanes (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
        pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv) ⦄ := by
  rw [pairwise_dispatch_eq]
  have widthEq := widenWidth_val ty.widen
  have loopLaw := pairwise_loop (widenWidth ty.widen) 0#u32 signed x 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = pairwiseBits signed
      (laneBits (widenWidth ty.widen).val (2*j) x.bv) (laneBits (widenWidth ty.widen).val (2*j+1) x.bv))
    (by intro j valid a b aEq bEq; exact pairwise_word _ _ _ _ _ _ (by cases ty <;> decide) aEq bEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro out lanes
  cases ty <;> with_unfolding_all exact lanes
end Itasca.Runtime.Interp.Simd
