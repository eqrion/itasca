import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Spec.Simd.IntegerMinMax
import Itasca.Runtime.Interp.Simd.Float.TruncSat
import Itasca.Runtime.Interp.Numeric.Float.FloatPromote
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Interp.Numeric.Float
import Itasca.Runtime.Interp.Simd.Relations.PureRelation

/-!
Sections, each formerly its own module: Binary, Unary, PureEntries.
-/

/-! ## Binary -/

section

/-!
Floating-point binary lanes: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Float Binary Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def floatBinaryWord {F : Type} (floats : runtime.platform.FloatOps F) (width bin : U32) (a b : U64) :
    Result U64 :=
  if bin >= 6#u32 then do
    let choose ← if bin = 6#u32 then runtime.interp.float.compare_float 2#u16 b a width
      else runtime.interp.float.compare_float 2#u16 a b width
    if choose then Result.ok b else Result.ok a
  else if width = 32#u32 then do
    let index ← lift (UScalar.cast .U16 bin)
    let first ← lift (UScalar.cast .U32 a)
    let second ← lift (UScalar.cast .U32 b)
    let result ← runtime.interp.float.binary32 floats index first second
    Result.ok (UScalar.cast .U64 result)
  else do
    let index ← lift (UScalar.cast .U16 bin)
    runtime.interp.float.binary64 floats index a b

theorem float_binary_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (x y initial : U128) (width bin i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (R : Nat → BitVec width.val → Prop)
    (wordLaw : ∀ j, j < 128/width.val → ∀ a b : U64,
      a.val = (laneBits width.val j x.bv).toNat →
      b.val = (laneBits width.val j y.bv).toNat →
      floatBinaryWord floats width bin a b ⦃ value => R j (value.bv.setWidth width.val) ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits width.val j initial.bv)) :
    runtime.interp.simd.float_binary_lanes_loop floats x y width bin initial i ⦃ result =>
      ∀ j, j < 128/width.val → R j (laneBits width.val j result.bv) ⦄ := by
  unfold runtime.interp.simd.float_binary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val → R j (laneBits width.val j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.float_binary_lanes_loop.body
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
      step with lane y width index positive widthBound (by omega) as ⟨b,bEq⟩
      have bBits : b.val = (laneBits width.val index.val y.bv).toNat := by
        rw [lane_bits_to_nat]
        exact bEq
      with_unfolding_all change (Aeneas.Std.bind (floatBinaryWord floats width bin a b) _) ⦃ _ ⦄
      step with wordLaw index.val less a b aBits bBits as ⟨value,allowed⟩
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

/-! ## Simd Float Binary Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

def floatBinaryIndex (op : vbinop_Fnn_N) : U32 :=
  match op with
  | .ADD => 0#u32 | .SUB => 1#u32 | .MUL => 2#u32 | .DIV => 3#u32
  | .MIN => 4#u32 | .MAX => 5#u32 | .PMIN => 6#u32 | .PMAX => 7#u32

def floatBinaryNative (op : vbinop_Fnn_N) : Prop :=
  match op with | .PMIN | .PMAX => False | _ => True

theorem float_binary32_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vbinop_Fnn_N) (a b : U32) (native : floatBinaryNative op) :
    runtime.interp.float.binary32 floats (UScalar.cast .U16 (floatBinaryIndex op)) a b ⦃ result =>
      floatOfBits 32 result.val ∈ floatBinaryChoices 32 op (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  cases op with
  | ADD => exact binary32_add_sound floats laws a b
  | SUB => exact binary32_sub_sound floats laws a b
  | MUL => exact binary32_mul_sound floats laws a b
  | DIV => exact binary32_div_sound floats laws a b
  | MIN => exact binary32_min_sound floats a b
  | MAX => exact binary32_max_sound floats a b
  | PMIN | PMAX => contradiction

theorem float_binary64_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (op : vbinop_Fnn_N) (a b : U64) (native : floatBinaryNative op) :
    runtime.interp.float.binary64 floats (UScalar.cast .U16 (floatBinaryIndex op)) a b ⦃ result =>
      floatOfBits 64 result.val ∈ floatBinaryChoices 64 op (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  cases op with
  | ADD => exact binary64_add_sound floats laws a b
  | SUB => exact binary64_sub_sound floats laws a b
  | MUL => exact binary64_mul_sound floats laws a b
  | DIV => exact binary64_div_sound floats laws a b
  | MIN => exact binary64_min_sound floats a b
  | MAX => exact binary64_max_sound floats a b
  | PMIN | PMAX => contradiction

theorem float_word_bits (ty : Fnn) (bits : U64) (bound : bits.val < 2^lsize (lanetype_Fnn ty)) :
    (bits.bv.setWidth (lsize (lanetype_Fnn ty))).toNat = bits.val := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt bound

theorem float_binary_native_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (a b : U64)
    (native : floatBinaryNative op)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex op) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  have small : ¬ floatBinaryIndex op >= 6#u32 := by cases op <;> simp_all [floatBinaryIndex,floatBinaryNative]
  unfold floatBinaryWord
  rw [if_neg small]
  cases ty with
  | F32 =>
    simp only [floatCompareWidth,if_true,lift,bind_ok]
    step with float_binary32_word floats laws op (UScalar.cast .U32 a) (UScalar.cast .U32 b) native as ⟨result,allowed⟩
    have aEq : (UScalar.cast .U32 a).val = a.val := by rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt aBound
    have bEq : (UScalar.cast .U32 b).val = b.val := by rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt bBound
    have outputEq : ((UScalar.cast .U64 result).bv.setWidth 32).toNat = result.val := by
      rw [BitVec.toNat_setWidth]
      change (UScalar.cast .U64 result).val%2^32 = result.val
      rw [U32.cast_U64_val_eq,Nat.mod_eq_of_lt (show result.val < 2^32 from result.bv.isLt)]
    change floatOfBits 32 ((UScalar.cast .U64 result).bv.setWidth 32).toNat ∈ _
    rw [outputEq]
    rw [aEq,bEq] at allowed
    exact allowed
  | F64 =>
    simp only [floatCompareWidth,show ¬(64#u32 = 32#u32) by decide,if_false,lift,bind_ok]
    apply WP.spec_mono (float_binary64_word floats laws op a b native)
    intro result allowed
    exact allowed

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Binary Pseudo -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

theorem float_binary_pmin {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex .PMIN) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) .PMIN
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  unfold floatBinaryWord floatBinaryIndex
  simp only [show 6#u32 >= 6#u32 by decide,if_true]
  with_unfolding_all change (Aeneas.Std.bind (runtime.interp.float.compare_float (floatCompareIndex .LT) b a (floatCompareWidth ty)) _) ⦃ _ ⦄
  step with float_compare_word ty .LT b a bBound aBound as ⟨answer,effect⟩
  rw [effect]
  split
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty b bBound,floatBinaryChoices,fpmin_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_pos chosen).symm
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty a aBound,floatBinaryChoices,fpmin_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_neg chosen).symm

theorem float_binary_pmax {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex .PMAX) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) .PMAX
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  unfold floatBinaryWord floatBinaryIndex
  simp only [show 7#u32 >= 6#u32 by decide,if_true]
  simp only [show ¬(7#u32 = 6#u32) by decide,if_false]
  with_unfolding_all change (Aeneas.Std.bind (runtime.interp.float.compare_float (floatCompareIndex .LT) a b (floatCompareWidth ty)) _) ⦃ _ ⦄
  step with float_compare_word ty .LT a b aBound bBound as ⟨answer,effect⟩
  rw [effect]
  split
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty b bBound,floatBinaryChoices,fpmax_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_pos chosen).symm
  · rename_i chosen
    simp only [WP.spec_ok,float_word_bits ty a aBound,floatBinaryChoices,fpmax_,List.mem_singleton]
    simpa only [floatComparisonBool] using (if_neg chosen).symm

theorem float_binary_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (a b : U64)
    (aBound : a.val < 2^lsize (lanetype_Fnn ty)) (bBound : b.val < 2^lsize (lanetype_Fnn ty)) :
    floatBinaryWord floats (floatCompareWidth ty) (floatBinaryIndex op) a b ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) (result.bv.setWidth (lsize (lanetype_Fnn ty))).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) (floatOfBits (lsize (lanetype_Fnn ty)) b.val) ⦄ := by
  cases op
  all_goals first
    | exact float_binary_pmin floats ty a b aBound bBound
    | exact float_binary_pmax floats ty a b aBound bBound
    | exact float_binary_native_word floats laws ty _ a b (by trivial) aBound bBound

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Binary Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd Platform

def floatBinaryOpcode (ty : Fnn) (op : vbinop_Fnn_N) : U32 :=
  match ty,op with
  | .F32,.ADD => 228#u32
  | .F32,.SUB => 229#u32
  | .F32,.MUL => 230#u32
  | .F32,.DIV => 231#u32
  | .F32,.MIN => 232#u32
  | .F32,.MAX => 233#u32
  | .F32,.PMIN => 234#u32
  | .F32,.PMAX => 235#u32
  | .F64,.ADD => 240#u32
  | .F64,.SUB => 241#u32
  | .F64,.MUL => 242#u32
  | .F64,.DIV => 243#u32
  | .F64,.MIN => 244#u32
  | .F64,.MAX => 245#u32
  | .F64,.PMIN => 246#u32
  | .F64,.PMAX => 247#u32

theorem float_binary_loop_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes_loop floats x y (floatCompareWidth ty) (floatBinaryIndex op) 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat) ⦄ := by
  have widthEq := float_compare_width_val ty
  rw [←widthEq]
  apply float_binary_loop floats x y 0#u128 (floatCompareWidth ty) (floatBinaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat ∈
      floatBinaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat)
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j y.bv).toNat))
  · intro j valid a b aEq bEq
    rw [widthEq] at aEq bEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    have secondBound : b.val < 2^lsize (lanetype_Fnn ty) := by rw [bEq]; exact BitVec.isLt _
    simpa only [aEq,bEq] using float_binary_word floats laws ty op a b bound secondBound
  · simp
  · simp

theorem float_binary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y =
      (runtime.interp.simd.float_binary_lanes_loop floats x
        y (floatCompareWidth ty) (floatBinaryIndex op) 0#u128 0#u32) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.float_binary_lanes floatBinaryOpcode floatCompareWidth floatBinaryIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem float_binary_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat) ⦄ := by
  rw [float_binary_dispatch_eq]
  apply WP.spec_mono (float_binary_loop_sound floats laws ty op x y)
  intro result allowed
  simpa using allowed

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Binary Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_binary_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_binary_lanes floats laws ty op x y)
  intro result allowed
  exact Spec.Simd.float_binary_step ty op x.bv y.bv result.bv allowed

theorem float_binary_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vbinop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatBinaryOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_binary_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_binary_simd_eq]
  step with float_binary_lanes_sound floats laws ty op x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Unary -/

section

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

end

/-! ## PureEntries -/

section

/-!
Source correspondence of pure floating-point opcode entries.

Main declarations: `pure_entry_103` and `pure_entry_247`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_103 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 103#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure103 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .CEIL offset laneIndex bits x y z memory

theorem pure_entry_104 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 104#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure104 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .FLOOR offset laneIndex bits x y z memory

theorem pure_entry_105 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 105#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure105 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .TRUNC offset laneIndex bits x y z memory

theorem pure_entry_106 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 106#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure106 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .NEAREST offset laneIndex bits x y z memory

theorem pure_entry_116 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 116#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure116 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .CEIL offset laneIndex bits x y z memory

theorem pure_entry_117 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 117#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure117 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .FLOOR offset laneIndex bits x y z memory

theorem pure_entry_122 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 122#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure122 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .TRUNC offset laneIndex bits x y z memory

theorem pure_entry_148 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 148#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure148 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .NEAREST offset laneIndex bits x y z memory

theorem pure_entry_224 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 224#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure224 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .ABS offset laneIndex bits x y z memory

theorem pure_entry_225 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 225#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure225 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .NEG offset laneIndex bits x y z memory

theorem pure_entry_227 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 227#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure227 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .SQRT offset laneIndex bits x y z memory

theorem pure_entry_228 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 228#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure228 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .ADD offset laneIndex bits x y z memory

theorem pure_entry_229 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 229#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure229 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .SUB offset laneIndex bits x y z memory

theorem pure_entry_230 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 230#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure230 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MUL offset laneIndex bits x y z memory

theorem pure_entry_231 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 231#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure231 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .DIV offset laneIndex bits x y z memory

theorem pure_entry_232 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 232#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure232 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MIN offset laneIndex bits x y z memory

theorem pure_entry_233 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 233#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure233 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MAX offset laneIndex bits x y z memory

theorem pure_entry_234 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 234#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure234 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .PMIN offset laneIndex bits x y z memory

theorem pure_entry_235 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 235#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure235 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .PMAX offset laneIndex bits x y z memory

theorem pure_entry_236 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 236#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure236 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .ABS offset laneIndex bits x y z memory

theorem pure_entry_237 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 237#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure237 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .NEG offset laneIndex bits x y z memory

theorem pure_entry_239 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 239#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure239 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .SQRT offset laneIndex bits x y z memory

theorem pure_entry_240 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 240#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure240 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .ADD offset laneIndex bits x y z memory

theorem pure_entry_241 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 241#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure241 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .SUB offset laneIndex bits x y z memory

theorem pure_entry_242 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 242#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure242 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MUL offset laneIndex bits x y z memory

theorem pure_entry_243 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 243#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure243 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .DIV offset laneIndex bits x y z memory

theorem pure_entry_244 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 244#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure244 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MIN offset laneIndex bits x y z memory

theorem pure_entry_245 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 245#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure245 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MAX offset laneIndex bits x y z memory

theorem pure_entry_246 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 246#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure246 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .PMIN offset laneIndex bits x y z memory

theorem pure_entry_247 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 247#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure247 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .PMAX offset laneIndex bits x y z memory

end Itasca.Runtime.Interp.Simd

end
