import SpecExt.Builtins.Float.Canonical

/-! Well-formedness of the complete arithmetic result sets, including every
permitted sign and payload of a nondeterministic NaN result. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem magnitude_wf {width : Nat} {value : fN} (h : wf_fN width value) :
    wf_fNmag width (magnitude value) := by
  cases h <;> assumption

theorem withSign_wf {width : Nat} {value : fNmag} (h : wf_fNmag width value)
    (sign : Bool) : wf_fN width (withSign sign value) := by
  cases sign
  · exact .fN_case_0 _ _ h
  · exact .fN_case_1 _ _ h

theorem zero_wf (width : Nat) : wf_fNmag width (.SUBNORM 0) :=
  .fNmag_case_1 width _ 0 ⟨Nat.two_pow_pos _, rfl⟩

theorem roundMagnitude_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (square : Bool) (q : Rat) : wf_fNmag width (roundMagnitude width square q) := by
  unfold roundMagnitude
  exact magnitude_wf (floatOfBits_wf width hw _)

theorem round_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) (negativeZero : Bool) : wf_fN width (round width q negativeZero) := by
  unfold round
  split_ifs
  · exact withSign_wf (zero_wf width) _
  · exact .fN_case_1 _ _ (roundMagnitude_wf width hw _ _)
  · exact .fN_case_0 _ _ (roundMagnitude_wf width hw _ _)

theorem roundSqrt_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) : wf_fN width (roundSqrt width q) :=
  .fN_case_0 _ _ (roundMagnitude_wf width hw _ _)

theorem nan_payload_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (offset : Nat) (h : offset < canon_ width) :
    wf_fNmag width (.NAN (canon_ width + offset)) := by
  apply wf_fNmag.fNmag_case_3
  rcases hw with rfl | rfl
  · change offset < 4194304 at h
    change 1 ≤ 4194304 + offset ∧ 4194304 + offset < 8388608
    omega
  · change offset < 2251799813685248 at h
    change 1 ≤ 2251799813685248 + offset ∧ 2251799813685248 + offset < 4503599627370496
    omega

theorem canonicalNaNs_wf (width : Nat) (hw : width = 32 ∨ width = 64) :
    Forall (wf_fN width) (canonicalNaNs width) := by
  intro value hv
  have hn : wf_fNmag width (.NAN (canon_ width)) := by
    simpa using nan_payload_wf width hw 0 (canonical_positive width hw)
  simp only [canonicalNaNs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .fN_case_0 _ _ hn
  · exact .fN_case_1 _ _ hn

theorem arithmeticNaNs_wf (width : Nat) (hw : width = 32 ∨ width = 64) :
    Forall (wf_fN width) (arithmeticNaNs width) := by
  intro value hv
  obtain ⟨offset, ho, hv⟩ := List.mem_flatMap.mp hv
  have hn := nan_payload_wf width hw offset (List.mem_range.mp ho)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .fN_case_0 _ _ hn
  · exact .fN_case_1 _ _ hn

theorem nans_wf (width : Nat) (hw : width = 32 ∨ width = 64) (inputs : List fN) :
    Forall (wf_fN width) (nans width inputs) := by
  unfold nans
  split
  · exact canonicalNaNs_wf width hw
  · exact arithmeticNaNs_wf width hw

theorem singleton_wf {width : Nat} {value : fN} (h : wf_fN width value) :
    Forall (wf_fN width) [value] := by
  intro v hv
  simpa only [List.mem_singleton.mp hv] using h

theorem add_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fadd_ width a b) := by
  unfold fadd_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf hb
  · exact singleton_wf (round_wf width hw _ _)

theorem sub_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fsub_ width a b) := by
  unfold fsub_
  split
  · exact nans_wf width hw _
  · exact add_wf width hw _ _ ha (withSign_wf (magnitude_wf hb) _)

theorem mul_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    Forall (wf_fN width) (fmul_ width a b) := by
  unfold fmul_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (.fNmag_case_2 width) _)
  · exact singleton_wf (round_wf width hw _ _)

theorem div_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    Forall (wf_fN width) (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (.fNmag_case_2 width) _)
  · exact singleton_wf (withSign_wf (zero_wf width) _)
  · exact singleton_wf (round_wf width hw _ _)

theorem sqrt_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a : fN)
    (ha : wf_fN width a) : Forall (wf_fN width) (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf (roundSqrt_wf width hw _)

theorem integral_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (op : Rat → Int) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (integral op width a) := by
  unfold integral
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf (round_wf width hw _ _)

end SpecExt.Builtins.Float
