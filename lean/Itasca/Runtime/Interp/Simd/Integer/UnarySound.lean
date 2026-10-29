import Itasca.Runtime.Interp.Simd.Integer.UnaryWords
import Itasca.Runtime.Interp.Simd.Integer.UnaryBits
import Itasca.Runtime.Spec.Simd.Unary
import SpecExt.Builtins.LaneMap

/-!
Packed and source correspondence for signed unary lane actions.

Main declarations: `signedUnaryAction`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

def signedUnaryAction : SignedUnaryKind → UnaryAction
  | .absolute => .absolute | .negate => .negate

theorem signed_unary_packed (ty : Jnn) (kind : SignedUnaryKind) (x result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        unaryLane (unaryAction (signedUnaryAction kind)) (lsize (lanetype_Jnn ty))
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv)) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind x.bv).map (lane_.mk_lane__0 ty)) := by
  have laneValue (j : Nat) (valid : j < 128/lsize (lanetype_Jnn ty)) :
      result.bv.toNat / 2^(lsize (lanetype_Jnn ty)*j) % 2^lsize (lanetype_Jnn ty) =
        (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) x.bv j)).toNat := by
    rw [←lane_bits_to_nat,lanes j valid]
    apply congrArg BitVec.toNat
    cases kind with
    | absolute => exact unary_lane_abs _ _ (by cases ty <;> decide)
    | negate => exact unary_lane_neg _ _ (by cases ty <;> decide)
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) x.bv j)).toNat) laneValue
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  refine packed.symm.trans ?_
  apply congrArg (packLanes (lanetype_Jnn ty))
  simp only [signedUnaryWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j member
  cases ty <;> rfl

@[step] theorem signed_unary_lanes_sound (ty : Jnn) (kind : SignedUnaryKind) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty (signedUnaryAction kind)) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),signedUnarySource ty kind]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty (signedUnaryAction kind) x)
  intro result outcome
  apply signed_unary_step ty kind x.bv result.bv
  apply signed_unary_packed ty kind x result
  cases kind <;> exact outcome

theorem signed_unary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : SignedUnaryKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty (signedUnaryAction kind)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty (signedUnaryAction kind)) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases kind <;> unfold runtime.interp.simd.simd unaryOpcode signedUnaryAction <;> with_unfolding_all rfl

@[step] theorem signed_unary_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : SignedUnaryKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty (signedUnaryAction kind)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),signedUnarySource ty kind]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [signed_unary_dispatch_eq]
  step with signed_unary_lanes_sound ty kind x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd
