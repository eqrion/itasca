import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc32
import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc64
import Itasca.Runtime.Spec.FloatTrunc

/-!
Scalar float-to-integer truncation and its source outcome. Signed, unsigned, trapping and saturating cases retain their separate domain checks and result bounds.
-/

/-! ## Float Trunc Scalar -/

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float
@[step] theorem scalar_i32_trunc_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 168#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 168#u16 >= 256#u16 then
    168#u16 - 256#u16 >>= fun i =>
      (if 168#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 168#u16 <= 171#u16 then
      168#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 168#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬168#u16 ≥ 256#u16 from by decide, show 168#u16 ≤ 171#u16 from by decide, show 168#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 true false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 169#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 169#u16 >= 256#u16 then
    169#u16 - 256#u16 >>= fun i =>
      (if 169#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 169#u16 <= 171#u16 then
      169#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 169#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬169#u16 ≥ 256#u16 from by decide, show 169#u16 ≤ 171#u16 from by decide, show 169#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 false false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 170#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 32 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 170#u16 >= 256#u16 then
    170#u16 - 256#u16 >>= fun i =>
      (if 170#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 170#u16 <= 171#u16 then
      170#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 170#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 32 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬170#u16 ≥ 256#u16 from by decide, show 170#u16 ≤ 171#u16 from by decide, show 170#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 true false (Or.inl rfl)

@[step] theorem scalar_i32_trunc_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 171#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 32 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 171#u16 >= 256#u16 then
    171#u16 - 256#u16 >>= fun i =>
      (if 171#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 171#u16 <= 171#u16 then
      171#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 171#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 32 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬171#u16 ≥ 256#u16 from by decide, show 171#u16 ≤ 171#u16 from by decide, show 171#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 false false (Or.inl rfl)

@[step] theorem scalar_i64_trunc_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 174#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 174#u16 >= 256#u16 then
    174#u16 - 256#u16 >>= fun i =>
      (if 174#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 174#u16 <= 171#u16 then
      174#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 174#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬174#u16 ≥ 256#u16 from by decide, show ¬174#u16 ≤ 171#u16 from by decide, show 174#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 true false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 175#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 175#u16 >= 256#u16 then
    175#u16 - 256#u16 >>= fun i =>
      (if 175#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 175#u16 <= 171#u16 then
      175#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 175#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show ¬175#u16 ≥ 256#u16 from by decide, show ¬175#u16 ≤ 171#u16 from by decide, show 175#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 false false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 176#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 64 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 176#u16 >= 256#u16 then
    176#u16 - 256#u16 >>= fun i =>
      (if 176#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 176#u16 <= 171#u16 then
      176#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 176#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 64 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬176#u16 ≥ 256#u16 from by decide, show ¬176#u16 ≤ 171#u16 from by decide, show 176#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 true false (Or.inr rfl)

@[step] theorem scalar_i64_trunc_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 177#u16 a b ⦃ result =>
      TruncOutcome (trunc__ 64 64 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 177#u16 >= 256#u16 then
    177#u16 - 256#u16 >>= fun i =>
      (if 177#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 177#u16 <= 171#u16 then
      177#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 177#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc__ 64 64 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show ¬177#u16 ≥ 256#u16 from by decide, show ¬177#u16 ≤ 171#u16 from by decide, show 177#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 false false (Or.inr rfl)

@[step] theorem scalar_i32_trunc_sat_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 256#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 256#u16 >= 256#u16 then
    256#u16 - 256#u16 >>= fun i =>
      (if 256#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 256#u16 <= 171#u16 then
      256#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 256#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 32 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 256#u16 ≥ 256#u16 from by decide, show ¬256#u16 ≤ 171#u16 from by decide, show 256#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 0#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 true true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 257#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 257#u16 >= 256#u16 then
    257#u16 - 256#u16 >>= fun i =>
      (if 257#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 257#u16 <= 171#u16 then
      257#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 257#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 32 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 257#u16 ≥ 256#u16 from by decide, show ¬257#u16 ≤ 171#u16 from by decide, show 257#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 1#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 32#u32 false true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 258#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 32 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 258#u16 >= 256#u16 then
    258#u16 - 256#u16 >>= fun i =>
      (if 258#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 258#u16 <= 171#u16 then
      258#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 258#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 32 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show 258#u16 ≥ 256#u16 from by decide, show ¬258#u16 ≤ 171#u16 from by decide, show 258#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 2#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 true true (Or.inl rfl)

@[step] theorem scalar_i32_trunc_sat_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 259#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 32 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 259#u16 >= 256#u16 then
    259#u16 - 256#u16 >>= fun i =>
      (if 259#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 259#u16 <= 171#u16 then
      259#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 259#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 32 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show 259#u16 ≥ 256#u16 from by decide, show ¬259#u16 ≤ 171#u16 from by decide, show 259#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 3#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 32#u32 false true (Or.inl rfl)

@[step] theorem scalar_i64_trunc_sat_f32_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 260#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 260#u16 >= 256#u16 then
    260#u16 - 256#u16 >>= fun i =>
      (if 260#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 260#u16 <= 171#u16 then
      260#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 260#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 64 .S (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 260#u16 ≥ 256#u16 from by decide, show ¬260#u16 ≤ 171#u16 from by decide, show ¬260#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 4#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 0#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 true true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f32_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 261#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 261#u16 >= 256#u16 then
    261#u16 - 256#u16 >>= fun i =>
      (if 261#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 261#u16 <= 171#u16 then
      261#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 261#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 32 64 .U (floatOfBits 32 (UScalar.cast .U32 a).val)) result ⦄
  simp only [show 261#u16 ≥ 256#u16 from by decide, show ¬261#u16 ≤ 171#u16 from by decide, show ¬261#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 5#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 1#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int32_sound a 64#u32 false true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f64_s {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 262#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 64 .S (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 262#u16 >= 256#u16 then
    262#u16 - 256#u16 >>= fun i =>
      (if 262#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 262#u16 <= 171#u16 then
      262#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 262#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 64 .S (floatOfBits 64 a.val)) result ⦄
  simp only [show 262#u16 ≥ 256#u16 from by decide, show ¬262#u16 ≤ 171#u16 from by decide, show ¬262#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 6#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 2#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 0#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 true true (Or.inr rfl)

@[step] theorem scalar_i64_trunc_sat_f64_u {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 263#u16 a b ⦃ result =>
      TruncOutcome (trunc_sat__ 64 64 .U (floatOfBits 64 a.val)) result ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change ((if 263#u16 >= 256#u16 then
    263#u16 - 256#u16 >>= fun i =>
      (if 263#u16 < 260#u16 then Result.ok 32#u32 else Result.ok 64#u32) >>= fun w =>
      Result.ok (i, w, true)
    else (if 263#u16 <= 171#u16 then
      263#u16 - 168#u16 >>= fun i => Result.ok (i, 32#u32)
      else 263#u16 - 174#u16 >>= fun i => Result.ok (i, 64#u32)) >>= fun (i, w) =>
        Result.ok (i, w, false)) >>= fun (op, width, saturating) =>
    op % 4#u16 >>= fun i => op % 2#u16 >>= fun j =>
    runtime.interp.float.trunc_int a (i < 2#u16) width (j = 0#u16) saturating) ⦃ result => TruncOutcome (trunc_sat__ 64 64 .U (floatOfBits 64 a.val)) result ⦄
  simp only [show 263#u16 ≥ 256#u16 from by decide, show ¬263#u16 ≤ 171#u16 from by decide, show ¬263#u16 < 260#u16 from by decide, ↓reduceIte]
  step as ⟨op, opEq⟩
  have opValue : op = 7#u16 := by scalar_tac
  subst op
  step as ⟨i, iEq⟩
  have iValue : i = 3#u16 := by scalar_tac
  subst i
  step as ⟨j, jEq⟩
  have jValue : j = 1#u16 := by scalar_tac
  subst j
  exact trunc_int64_sound a 64#u32 false true (Or.inr rfl)

end Itasca.Runtime.Interp

end

/-! ## Float Trunc Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

def TruncSourceOutcome (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError) : Prop :=
  let instructions := [admininstr.CONST (numtype_Fnn source) (.mk_num__1 source input),
    .CVTOP (numtype_Inn target) (numtype_Fnn source)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))]
  match result with
  | .Ok value => Step_pure instructions [.CONST (numtype_Inn target) (.mk_num__0 target (.mk_uN value.val))]
  | .Err (.Trap reason) => Step_pure instructions [.TRAP] ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem truncOutcome_source (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError)
    (inputWf : wf_fN (sizenn (numtype_Fnn source)) input)
    (effect : TruncOutcome (if saturating then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input) result) :
    TruncSourceOutcome source target sign saturating input result := by
  cases result with
  | Ok value => exact Spec.float_truncation_pure source target sign saturating input _ effect inputWf
  | Err error =>
    cases error <;> simp only [TruncOutcome] at effect
    case Trap reason =>
      exact ⟨Spec.float_truncation_pure source target sign saturating input none effect.1 inputWf, effect.2⟩

theorem scalar_i32_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 168#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .S false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 169#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .U false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 170#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .S false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 171#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .U false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 174#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .S false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 175#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .U false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 176#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .S false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 177#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .U false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 256#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .S true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 257#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .U true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 258#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .S true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 259#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .U true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 260#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .S true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 261#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .U true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 262#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .S true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 263#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .U true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

end Itasca.Runtime.Interp

end
