import Itasca.Runtime.Platform.Laws
import SpecExt.Builtins.Float.PromotionFirst

/-! A specification-level float dictionary choosing the first permitted result.
This witnesses consistency of the platform contract, not correctness of libm. -/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

private theorem reply_nonempty {width : Nat} {allowed : List fN}
    (family : ReplyFamily width allowed) (positive : 0 < canon_ width) : allowed ≠ [] := by
  cases family with
  | singleton value => exact List.cons_ne_nil _ _
  | canonical => exact List.cons_ne_nil _ _
  | arithmetic =>
    intro empty
    have head := arithmeticNaNs_head width positive
    rw [empty] at head
    cases head

private def firstReply (allowed : List fN) : fN := allowed.headD (.POS (.SUBNORM 0))

private theorem firstReply_mem {width : Nat} {allowed : List fN}
    (family : ReplyFamily width allowed) (positive : 0 < canon_ width) :
    firstReply allowed ∈ allowed := by
  have nonempty := reply_nonempty family positive
  cases allowed with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => exact List.mem_cons_self

private theorem outcome_of_member {value : fN} {allowed : List fN}
    (member : value ∈ allowed) : FloatOutcome value allowed := by
  unfold FloatOutcome
  by_cases nan : isNaN value = true
  · exact if_pos nan ▸ ⟨value, member, nan⟩
  · exact if_neg nan ▸ member

private def first32 (allowed : List fN) (family : ReplyFamily 32 allowed)
    (valid : Forall (wf_fN 32) allowed) : Aeneas.Std.Result U32 :=
  .ok (UScalar.ofNatCore (floatBits 32 (firstReply allowed))
    (floatBits_lt_32 _ (valid _ (firstReply_mem family (by decide)))))

private def first64 (allowed : List fN) (family : ReplyFamily 64 allowed)
    (valid : Forall (wf_fN 64) allowed) : Aeneas.Std.Result U64 :=
  .ok (UScalar.ofNatCore (floatBits 64 (firstReply allowed))
    (floatBits_lt_64 _ (valid _ (firstReply_mem family (by decide)))))

private theorem first32_spec (allowed : List fN) (family : ReplyFamily 32 allowed)
    (valid : Forall (wf_fN 32) allowed) :
    first32 allowed family valid ⦃ result => FloatOutcome (floatOfBits 32 result.val) allowed ⦄ := by
  simp only [first32, WP.spec_ok, UScalar.ofNatCore_val_eq]
  rw [float_roundtrip_32 _ (valid _ (firstReply_mem family (by decide)))]
  exact outcome_of_member (firstReply_mem family (by decide))

private theorem first64_spec (allowed : List fN) (family : ReplyFamily 64 allowed)
    (valid : Forall (wf_fN 64) allowed) :
    first64 allowed family valid ⦃ result => FloatOutcome (floatOfBits 64 result.val) allowed ⦄ := by
  simp only [first64, WP.spec_ok, UScalar.ofNatCore_val_eq]
  rw [float_roundtrip_64 _ (valid _ (firstReply_mem family (by decide)))]
  exact outcome_of_member (firstReply_mem family (by decide))

private theorem special_wf (target : Nat) (value : fN)
    (special : isInf value || isZero value) : wf_fN target value := by
  have choice : magnitude value = .INF ∨ magnitude value = .SUBNORM 0 := by
    simpa only [isInf, isZero, Bool.or_eq_true, beq_iff_eq] using special
  cases value <;> simp only [magnitude] at choice
  all_goals rcases choice with rfl | rfl
  all_goals first
    | exact .fN_case_0 _ _ (.fNmag_case_2 _)
    | exact .fN_case_1 _ _ (.fNmag_case_2 _)
    | exact .fN_case_0 _ _ (zero_wf target)
    | exact .fN_case_1 _ _ (zero_wf target)

private theorem demotion_wf (source target : Nat) (width : target = 32 ∨ target = 64)
    (value : fN) : Forall (wf_fN target) (demote__ source target value) := by
  unfold demote__
  split_ifs with nan canonical special
  · exact canonicalNaNs_wf target width
  · exact arithmeticNaNs_wf target width
  · exact singleton_wf (special_wf target value special)
  · exact singleton_wf (round_wf target width _ _)

private theorem conversion_wf (source target : Nat) (width : target = 32 ∨ target = 64)
    (sign : sx) (value : iN) : Forall (wf_fN target) [convert__ source target sign value] :=
  singleton_wf (round_wf target width _ _)

/-- A mathematical implementation selecting the first permitted floating-point result. -/
noncomputable def floatWitness : runtime.platform.FloatOps Unit where
  f32_add a b := first32 (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (add_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (add_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (Or.inl rfl) a.val) (floatOfBits_wf 32 (Or.inl rfl) b.val))
  f32_sub a b := first32 (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (sub_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (sub_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (Or.inl rfl) a.val) (floatOfBits_wf 32 (Or.inl rfl) b.val))
  f32_mul a b := first32 (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (mul_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (mul_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val))
  f32_div a b := first32 (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (div_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (div_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val))
  f32_sqrt a := first32 (fsqrt_ 32 (floatOfBits 32 a.val))
    (sqrt_reply_family 32 (floatOfBits 32 a.val)) (sqrt_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_ceil a := first32 (fceil_ 32 (floatOfBits 32 a.val))
    (ceil_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_floor a := first32 (ffloor_ 32 (floatOfBits 32 a.val))
    (floor_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_trunc a := first32 (ftrunc_ 32 (floatOfBits 32 a.val))
    (trunc_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_nearest a := first32 (fnearest_ 32 (floatOfBits 32 a.val))
    (nearest_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_convert_i32_s a := first32 [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 a).val)]
    (.singleton _) (conversion_wf 32 32 (Or.inl rfl) .S (.mk_uN (IScalar.hcast .U32 a).val))
  f32_convert_i32_u a := first32 [convert__ 32 32 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 32 32 (Or.inl rfl) .U (.mk_uN a.val))
  f32_convert_i64_s a := first32 [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 a).val)]
    (.singleton _) (conversion_wf 64 32 (Or.inl rfl) .S (.mk_uN (IScalar.hcast .U64 a).val))
  f32_convert_i64_u a := first32 [convert__ 64 32 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 64 32 (Or.inl rfl) .U (.mk_uN a.val))
  f64_add a b := first64 (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (add_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (add_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (Or.inr rfl) a.val) (floatOfBits_wf 64 (Or.inr rfl) b.val))
  f64_sub a b := first64 (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (sub_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (sub_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (Or.inr rfl) a.val) (floatOfBits_wf 64 (Or.inr rfl) b.val))
  f64_mul a b := first64 (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (mul_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (mul_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val))
  f64_div a b := first64 (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (div_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (div_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val))
  f64_sqrt a := first64 (fsqrt_ 64 (floatOfBits 64 a.val))
    (sqrt_reply_family 64 (floatOfBits 64 a.val)) (sqrt_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_ceil a := first64 (fceil_ 64 (floatOfBits 64 a.val))
    (ceil_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_floor a := first64 (ffloor_ 64 (floatOfBits 64 a.val))
    (floor_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_trunc a := first64 (ftrunc_ 64 (floatOfBits 64 a.val))
    (trunc_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_nearest a := first64 (fnearest_ 64 (floatOfBits 64 a.val))
    (nearest_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_convert_i32_s a := first64 [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 a).val)]
    (.singleton _) (conversion_wf 32 64 (Or.inr rfl) .S (.mk_uN (IScalar.hcast .U32 a).val))
  f64_convert_i32_u a := first64 [convert__ 32 64 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 32 64 (Or.inr rfl) .U (.mk_uN a.val))
  f64_convert_i64_s a := first64 [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 a).val)]
    (.singleton _) (conversion_wf 64 64 (Or.inr rfl) .S (.mk_uN (IScalar.hcast .U64 a).val))
  f64_convert_i64_u a := first64 [convert__ 64 64 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 64 64 (Or.inr rfl) .U (.mk_uN a.val))
  f32_demote_f64 a := first32 (demote__ 64 32 (floatOfBits 64 a.val))
    (demote_reply_family 64 32 _) (demotion_wf 64 32 (Or.inl rfl) _)

/-- The first-result dictionary satisfies every operation of the platform contract. -/
theorem floatWitness_correct : FloatOpsCorrect floatWitness where
  f32_add a b := first32_spec (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (add_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (add_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (Or.inl rfl) a.val) (floatOfBits_wf 32 (Or.inl rfl) b.val))
  f32_sub a b := first32_spec (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (sub_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (sub_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (Or.inl rfl) a.val) (floatOfBits_wf 32 (Or.inl rfl) b.val))
  f32_mul a b := first32_spec (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (mul_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (mul_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val))
  f32_div a b := first32_spec (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val))
    (div_reply_family 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) (div_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits 32 b.val))
  f32_sqrt a := first32_spec (fsqrt_ 32 (floatOfBits 32 a.val))
    (sqrt_reply_family 32 (floatOfBits 32 a.val)) (sqrt_wf 32 (Or.inl rfl) (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_ceil a := first32_spec (fceil_ 32 (floatOfBits 32 a.val))
    (ceil_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_floor a := first32_spec (ffloor_ 32 (floatOfBits 32 a.val))
    (floor_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_trunc a := first32_spec (ftrunc_ 32 (floatOfBits 32 a.val))
    (trunc_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_nearest a := first32_spec (fnearest_ 32 (floatOfBits 32 a.val))
    (nearest_reply_family 32 (floatOfBits 32 a.val)) (integral_wf 32 (Or.inl rfl) _ (floatOfBits 32 a.val) (floatOfBits_wf 32 (Or.inl rfl) a.val))
  f32_convert_i32_s a := first32_spec [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 a).val)]
    (.singleton _) (conversion_wf 32 32 (Or.inl rfl) .S (.mk_uN (IScalar.hcast .U32 a).val))
  f32_convert_i32_u a := first32_spec [convert__ 32 32 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 32 32 (Or.inl rfl) .U (.mk_uN a.val))
  f32_convert_i64_s a := first32_spec [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 a).val)]
    (.singleton _) (conversion_wf 64 32 (Or.inl rfl) .S (.mk_uN (IScalar.hcast .U64 a).val))
  f32_convert_i64_u a := first32_spec [convert__ 64 32 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 64 32 (Or.inl rfl) .U (.mk_uN a.val))
  f64_add a b := first64_spec (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (add_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (add_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (Or.inr rfl) a.val) (floatOfBits_wf 64 (Or.inr rfl) b.val))
  f64_sub a b := first64_spec (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (sub_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (sub_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (Or.inr rfl) a.val) (floatOfBits_wf 64 (Or.inr rfl) b.val))
  f64_mul a b := first64_spec (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (mul_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (mul_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val))
  f64_div a b := first64_spec (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val))
    (div_reply_family 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) (div_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits 64 b.val))
  f64_sqrt a := first64_spec (fsqrt_ 64 (floatOfBits 64 a.val))
    (sqrt_reply_family 64 (floatOfBits 64 a.val)) (sqrt_wf 64 (Or.inr rfl) (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_ceil a := first64_spec (fceil_ 64 (floatOfBits 64 a.val))
    (ceil_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_floor a := first64_spec (ffloor_ 64 (floatOfBits 64 a.val))
    (floor_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_trunc a := first64_spec (ftrunc_ 64 (floatOfBits 64 a.val))
    (trunc_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_nearest a := first64_spec (fnearest_ 64 (floatOfBits 64 a.val))
    (nearest_reply_family 64 (floatOfBits 64 a.val)) (integral_wf 64 (Or.inr rfl) _ (floatOfBits 64 a.val) (floatOfBits_wf 64 (Or.inr rfl) a.val))
  f64_convert_i32_s a := first64_spec [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 a).val)]
    (.singleton _) (conversion_wf 32 64 (Or.inr rfl) .S (.mk_uN (IScalar.hcast .U32 a).val))
  f64_convert_i32_u a := first64_spec [convert__ 32 64 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 32 64 (Or.inr rfl) .U (.mk_uN a.val))
  f64_convert_i64_s a := first64_spec [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 a).val)]
    (.singleton _) (conversion_wf 64 64 (Or.inr rfl) .S (.mk_uN (IScalar.hcast .U64 a).val))
  f64_convert_i64_u a := first64_spec [convert__ 64 64 .U (.mk_uN a.val)]
    (.singleton _) (conversion_wf 64 64 (Or.inr rfl) .U (.mk_uN a.val))
  f32_demote_f64 a := first32_spec (demote__ 64 32 (floatOfBits 64 a.val))
    (demote_reply_family 64 32 _) (demotion_wf 64 32 (Or.inl rfl) _)

end Itasca.Runtime.Platform
