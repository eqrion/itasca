import Itasca.Runtime.Interp.Simd.Lanes.Splat
import Itasca.Runtime.Interp.Simd.Lanes.Packing
import Itasca.Runtime.Interp.Simd.Float.CompareWords
import Itasca.Runtime.Spec.Simd.FloatUnary
import Itasca.Runtime.Interp.Numeric.Float

/-!
Floating-point unary lanes: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Float Unary Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def floatUnaryWord {F : Type} (floats : runtime.platform.FloatOps F) (width unary : U32) (a : U64) :
    Result U64 :=
  if width = 32#u32 then do
    let index ← lift (UScalar.cast .U16 unary)
    let bits ← lift (UScalar.cast .U32 a)
    let result ← runtime.interp.float.unary32 floats index bits
    Result.ok (UScalar.cast .U64 result)
  else do
    let index ← lift (UScalar.cast .U16 unary)
    runtime.interp.float.unary64 floats index a

theorem float_unary_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (x initial : U128) (width unary i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (R : Nat → BitVec width.val → Prop)
    (wordLaw : ∀ j, j < 128/width.val → ∀ a : U64,
      a.val = (laneBits width.val j x.bv).toNat →
      floatUnaryWord floats width unary a ⦃ value => R j (value.bv.setWidth width.val) ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits width.val j initial.bv)) :
    runtime.interp.simd.float_unary_lanes_loop floats x width unary initial i ⦃ result =>
      ∀ j, j < 128/width.val → R j (laneBits width.val j result.bv) ⦄ := by
  unfold runtime.interp.simd.float_unary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val → R j (laneBits width.val j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.float_unary_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane x width index positive widthBound (by omega) as ⟨a,aEq⟩
      have aBits : a.val = (laneBits width.val index.val x.bv).toNat := by
        rw [lane_bits_to_nat]
        exact aEq
      with_unfolding_all change (Aeneas.Std.bind (floatUnaryWord floats width unary a) _) ⦃ _ ⦄
      step with wordLaw index.val less a aBits as ⟨value,allowed⟩
      step with put_lanes current width index value positive widthBound range as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Unary Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

def floatUnaryIndex (op : vunop_Fnn_N) : U32 :=
  match op with
  | .ABS => 0#u32 | .NEG => 1#u32 | .CEIL => 2#u32 | .FLOOR => 3#u32
  | .TRUNC => 4#u32 | .NEAREST => 5#u32 | .SQRT => 6#u32

theorem float_unary32_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U32) :
    runtime.interp.float.unary32 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      floatOfBits 32 result.val ∈ floatUnaryChoices 32 op (floatOfBits 32 bits.val) ⦄ := by
  cases op with
  | ABS => exact unary32_abs_sound floats bits
  | NEG => exact unary32_neg_sound floats bits
  | SQRT => exact unary32_sqrt_sound floats laws bits
  | CEIL => exact unary32_ceil_sound floats laws bits
  | FLOOR => exact unary32_floor_sound floats laws bits
  | TRUNC => exact unary32_trunc_sound floats laws bits
  | NEAREST => exact unary32_nearest_sound floats laws bits

theorem float_unary64_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vunop_Fnn_N) (bits : U64) :
    runtime.interp.float.unary64 floats (UScalar.cast .U16 (floatUnaryIndex op)) bits ⦃ result =>
      floatOfBits 64 result.val ∈ floatUnaryChoices 64 op (floatOfBits 64 bits.val) ⦄ := by
  cases op with
  | ABS => exact unary64_abs_sound floats bits
  | NEG => exact unary64_neg_sound floats bits
  | SQRT => exact unary64_sqrt_sound floats laws bits
  | CEIL => exact unary64_ceil_sound floats laws bits
  | FLOOR => exact unary64_floor_sound floats laws bits
  | TRUNC => exact unary64_trunc_sound floats laws bits
  | NEAREST => exact unary64_nearest_sound floats laws bits

theorem float_unary_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (bits : U64)
    (bound : bits.val < 2^lsize (lanetype_Fnn ty)) :
    floatUnaryWord floats (floatCompareWidth ty) (floatUnaryIndex op) bits ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op (floatOfBits (lsize (lanetype_Fnn ty)) bits.val) ⦄ := by
  cases ty with
  | F32 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [if_true,lift,bind_ok]
    step with float_unary32_word floats laws op (UScalar.cast .U32 bits) as ⟨result,allowed⟩
    have inputEq : (UScalar.cast .U32 bits).val = bits.val := by
      change bits.val < 2^32 at bound
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt bound
    have outputEq : ((UScalar.cast .U64 result).bv.setWidth 32).toNat = result.val := by
      rw [BitVec.toNat_setWidth]
      change (UScalar.cast .U64 result).val%2^32 = result.val
      rw [U32.cast_U64_val_eq,Nat.mod_eq_of_lt (show result.val < 2^32 from result.bv.isLt)]
    change floatOfBits 32 ((UScalar.cast .U64 result).bv.setWidth 32).toNat ∈ _
    rw [outputEq]
    rw [inputEq] at allowed
    exact allowed
  | F64 =>
    unfold floatUnaryWord floatCompareWidth
    simp only [show ¬(64#u32 = 32#u32) by decide,if_false,lift,bind_ok]
    apply WP.spec_mono (float_unary64_word floats laws op bits)
    intro result allowed
    exact allowed

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Unary Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

def floatUnaryOpcode (ty : Fnn) (op : vunop_Fnn_N) : U32 :=
  match ty,op with
  | .F32,.ABS => 224#u32 | .F32,.NEG => 225#u32 | .F32,.SQRT => 227#u32
  | .F32,.CEIL => 103#u32 | .F32,.FLOOR => 104#u32 | .F32,.TRUNC => 105#u32 | .F32,.NEAREST => 106#u32
  | .F64,.ABS => 236#u32 | .F64,.NEG => 237#u32 | .F64,.SQRT => 239#u32
  | .F64,.CEIL => 116#u32 | .F64,.FLOOR => 117#u32 | .F64,.TRUNC => 122#u32 | .F64,.NEAREST => 148#u32

theorem float_unary_loop_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes_loop floats x (floatCompareWidth ty) (floatUnaryIndex op) 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat) ⦄ := by
  have widthEq := float_compare_width_val ty
  rw [←widthEq]
  apply float_unary_loop floats x 0#u128 (floatCompareWidth ty) (floatUnaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat ∈
      floatUnaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat))
  · intro j valid a aEq
    rw [widthEq] at aEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    simpa only [aEq] using float_unary_word floats laws ty op a bound
  · simp
  · simp

theorem float_unary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x =
      (runtime.interp.simd.float_unary_lanes_loop floats x
        (floatCompareWidth ty) (floatUnaryIndex op) 0#u128 0#u32) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.float_unary_lanes floatUnaryOpcode floatCompareWidth floatUnaryIndex
  all_goals with_unfolding_all first
    | change (Aeneas.Std.bind (Result.ok _) _) = _
    | change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _
  all_goals simp only [bind_ok]
  all_goals rfl

@[step] theorem float_unary_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat) ⦄ := by
  rw [float_unary_dispatch_eq]
  apply WP.spec_mono (float_unary_loop_sound floats laws ty op x)
  intro result allowed
  simpa using allowed

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Unary Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_unary_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VUNOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_unary_lanes floats laws ty op x)
  intro result allowed
  exact Spec.Simd.float_unary_step ty op x.bv result.bv allowed

theorem float_unary_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vunop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatUnaryOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_unary_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VUNOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_unary_simd_eq]
  step with float_unary_lanes_sound floats laws ty op x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end
