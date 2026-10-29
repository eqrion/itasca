import Itasca.Runtime.Interp.Simd.Lanes.Access
import Itasca.Runtime.Spec.Simd.Bitwise
import Itasca.Runtime.Spec.Simd.AnyTrue

/-!
Whole-vector bit operations: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Whole -/

section

set_option maxRecDepth 4096
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def binaryOpcode (op : vvbinop) : U32 :=
  match op with
  | .AND => 78#u32
  | .ANDNOT => 79#u32
  | .OR => 80#u32
  | .XOR => 81#u32

theorem binary_lanes_eq (op : vvbinop) (a b : U128) :
    runtime.interp.simd.bitwise_lanes (binaryOpcode op) a b =
      .ok ⟨Spec.Simd.binary op a.bv b.bv⟩ := by
  cases op <;> unfold runtime.interp.simd.bitwise_lanes binaryOpcode
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change ((Result.ok _) = _)
  all_goals rfl

@[step] theorem select_bits (a b c : U128) :
    runtime.interp.simd.select_bits a b c ⦃ result =>
      result.bv = (a.bv &&& c.bv) ||| (b.bv &&& ~~~c.bv) ⦄ := by
  simp only [runtime.interp.simd.select_bits,
    lift, bind_ok, WP.spec_ok, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not]

theorem not_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 77#u32 offset laneIndex bits a b c memory =
      .ok (.Ok (~~~a), memory) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change (Aeneas.Std.bind (lift (~~~a))
      (fun result => Result.ok (core.result.Result.Ok result, memory)) = _)
  rw [lift, bind_ok]

theorem binary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (op : vvbinop) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (binaryOpcode op) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.bitwise_lanes (binaryOpcode op) a b)
        (fun result => Result.ok (core.result.Result.Ok result, memory)) := by
  cases op <;> unfold runtime.interp.simd.simd binaryOpcode <;> with_unfolding_all rfl

@[step] theorem not_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 77#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧ value.bv = ~~~a.bv ⦄ := by
  rw [not_dispatch_eq]
  simp only [WP.spec_ok]
  exact ⟨~~~a, rfl, rfl⟩

@[step] theorem binary_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (op : vvbinop) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (binaryOpcode op) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        value.bv = Spec.Simd.binary op a.bv b.bv ⦄ := by
  rw [binary_dispatch_eq, binary_lanes_eq, bind_ok]
  simp only [WP.spec_ok]
  exact ⟨_, rfl, rfl⟩

@[step] theorem bitselect_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 82#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        value.bv = (a.bv &&& c.bv) ||| (b.bv &&& ~~~c.bv) ⦄ := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change
    (Aeneas.Std.bind (runtime.interp.simd.select_bits a b c)
      (fun result => Result.ok (core.result.Result.Ok result, memory))) ⦃ _ ⦄
  step as ⟨value, valueEq⟩
  exact ⟨_, rfl, valueEq⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Whole Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem any_true_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 83#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        value.val = if a.val ≠ 0 then 1 else 0 ⦄ := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change
    (Aeneas.Std.bind (lift (UScalar.cast_fromBool .U128 (a != 0#u128)))
      (fun result => Result.ok (core.result.Result.Ok result, memory))) ⦃ _ ⦄
  rw [lift, bind_ok]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [UScalar.cast_fromBool_val_eq]
  by_cases h : a.val = 0
  · have hz : a = 0#u128 := (UScalar.eq_equiv _ _).mpr h
    subst a
    decide
  · have hn : a ≠ 0#u128 := by intro hz; subst a; exact h rfl
    have hb : (a == 0#u128) = false := beq_eq_false_iff_ne.mpr hn
    simp [h, hb, bne, Bool.toNat, UScalar.size, UScalarTy.numBits]

theorem not_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 77#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val), .VVUNOP .V128 .NOT]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  apply WP.spec_mono (not_dispatch floats offset laneIndex bits a b c memory)
  rintro result ⟨value, exactResult, exactBits⟩
  refine ⟨value, exactResult, ?_⟩
  have h := Spec.Simd.not_step a.bv
  have eq := congrArg BitVec.toNat exactBits
  change value.val = _ at eq
  rw [eq]
  exact h

theorem binary_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (op : vvbinop) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (binaryOpcode op) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val), .VCONST .V128 (.mk_uN b.val),
          .VVBINOP .V128 op] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  apply WP.spec_mono (binary_dispatch floats op offset laneIndex bits a b c memory)
  rintro result ⟨value, exactResult, exactBits⟩
  refine ⟨value, exactResult, ?_⟩
  have eq := congrArg BitVec.toNat exactBits
  change value.val = _ at eq
  rw [eq]
  exact Spec.Simd.binary_step op a.bv b.bv

theorem bitselect_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 82#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val), .VCONST .V128 (.mk_uN b.val),
          .VCONST .V128 (.mk_uN c.val), .VVTERNOP .V128 .BITSELECT]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  apply WP.spec_mono (bitselect_dispatch floats offset laneIndex bits a b c memory)
  rintro result ⟨value, exactResult, exactBits⟩
  refine ⟨value, exactResult, ?_⟩
  have eq := congrArg BitVec.toNat exactBits
  change value.val = _ at eq
  rw [eq]
  exact Spec.Simd.bitselect_step a.bv b.bv c.bv

theorem any_true_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 83#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val), .VVTESTOP .V128 .ANY_TRUE]
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (any_true_dispatch floats offset laneIndex bits a b c memory)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.Simd.any_true_step a.bv

end Itasca.Runtime.Interp.Simd

end
