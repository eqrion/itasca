import Itasca.Generated.Types
import SpecExt.Builtins.Float.Canonical

/-! Exact embedding contract for the extracted float dictionary. Every method
returns normally. Finite/infinite results must belong to the specification set;
any raw NaN is allowed only when that set contains a NaN. Canonicalization is
an interpreter obligation, not an extra restriction on the embedding payload. -/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

def FloatOutcome (value : fN) (allowed : List fN) : Prop :=
  if isNaN value then ∃ choice ∈ allowed, isNaN choice = true else value ∈ allowed

theorem floatOutcome_nonNaN {value : fN} {allowed : List fN}
    (h : FloatOutcome value allowed) (hn : isNaN value = false) : value ∈ allowed := by
  simpa [FloatOutcome, hn] using h

theorem floatOutcome_NaN {value : fN} {allowed : List fN}
    (h : FloatOutcome value allowed) (hn : isNaN value = true) :
    ∃ choice ∈ allowed, isNaN choice = true := by
  simpa [FloatOutcome, hn] using h

/-- A1 for all 27 rounding operations in the actual extracted dictionary. -/
structure FloatOpsCorrect {F : Type} (ops : runtime.platform.FloatOps F) : Prop where
  f32_add : ∀ a b, ops.f32_add a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_sub : ∀ a b, ops.f32_sub a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_mul : ∀ a b, ops.f32_mul a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_div : ∀ a b, ops.f32_div a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_sqrt : ∀ a, ops.f32_sqrt a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fsqrt_ 32 (floatOfBits 32 a.val)) ⦄
  f32_ceil : ∀ a, ops.f32_ceil a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fceil_ 32 (floatOfBits 32 a.val)) ⦄
  f32_floor : ∀ a, ops.f32_floor a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (ffloor_ 32 (floatOfBits 32 a.val)) ⦄
  f32_trunc : ∀ a, ops.f32_trunc a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (ftrunc_ 32 (floatOfBits 32 a.val)) ⦄
  f32_nearest : ∀ a, ops.f32_nearest a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fnearest_ 32 (floatOfBits 32 a.val)) ⦄
  f32_convert_i32_s : ∀ a, ops.f32_convert_i32_s a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 a).val)] ⦄
  f32_convert_i32_u : ∀ a, ops.f32_convert_i32_u a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 32 32 .U (.mk_uN a.val)] ⦄
  f32_convert_i64_s : ∀ a, ops.f32_convert_i64_s a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 a).val)] ⦄
  f32_convert_i64_u : ∀ a, ops.f32_convert_i64_u a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 64 32 .U (.mk_uN a.val)] ⦄
  f64_add : ∀ a b, ops.f64_add a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_sub : ∀ a b, ops.f64_sub a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_mul : ∀ a b, ops.f64_mul a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_div : ∀ a b, ops.f64_div a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_sqrt : ∀ a, ops.f64_sqrt a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fsqrt_ 64 (floatOfBits 64 a.val)) ⦄
  f64_ceil : ∀ a, ops.f64_ceil a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fceil_ 64 (floatOfBits 64 a.val)) ⦄
  f64_floor : ∀ a, ops.f64_floor a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (ffloor_ 64 (floatOfBits 64 a.val)) ⦄
  f64_trunc : ∀ a, ops.f64_trunc a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (ftrunc_ 64 (floatOfBits 64 a.val)) ⦄
  f64_nearest : ∀ a, ops.f64_nearest a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fnearest_ 64 (floatOfBits 64 a.val)) ⦄
  f64_convert_i32_s : ∀ a, ops.f64_convert_i32_s a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 a).val)] ⦄
  f64_convert_i32_u : ∀ a, ops.f64_convert_i32_u a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 32 64 .U (.mk_uN a.val)] ⦄
  f64_convert_i64_s : ∀ a, ops.f64_convert_i64_s a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 a).val)] ⦄
  f64_convert_i64_u : ∀ a, ops.f64_convert_i64_u a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 64 64 .U (.mk_uN a.val)] ⦄
  f32_demote_f64 : ∀ a, ops.f32_demote_f64 a ⦃ result =>
    FloatOutcome (floatOfBits 32 result.val) (demote__ 64 32 (floatOfBits 64 a.val)) ⦄

theorem floatOutcome_canonicalize (width : Nat) (value : fN) (allowed : List fN)
    (h : FloatOutcome value allowed) (hc : CanonicalClosed width allowed) :
    (if isNaN value then fN.POS (.NAN (canon_ width)) else value) ∈ allowed := by
  cases hn : isNaN value
  · simpa [hn] using floatOutcome_nonNaN h hn
  · simpa [hn] using hc (floatOutcome_NaN h hn)

end Itasca.Runtime.Platform
