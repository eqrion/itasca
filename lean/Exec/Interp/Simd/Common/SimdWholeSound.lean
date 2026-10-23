import Exec.Interp.Simd.Common.SimdWhole
import Exec.Spec.SimdAnyTrue
namespace Exec.Interp.Simd
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

end Exec.Interp.Simd
