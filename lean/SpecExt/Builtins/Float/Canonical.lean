import SpecExt.Builtins.Float.RoundingLemmas
import SpecExt.Builtins.Float.Lemmas

/-! Arithmetic result sets remain valid after a wrapper replaces a permitted
NaN with the positive canonical NaN. This property is proved from the concrete
builtins; it is not an additional embedding assumption. -/

namespace SpecExt.Builtins.Float

/-- Closure under the interpreter's NaN replacement. -/
def CanonicalClosed (width : Nat) (allowed : List fN) : Prop :=
  (∃ choice ∈ allowed, isNaN choice = true) → .POS (.NAN (canon_ width)) ∈ allowed

theorem canonicalClosed_nans (width : Nat) (inputs : List fN) (h : 0 < canon_ width) :
    CanonicalClosed width (nans width inputs) := by
  intro _
  exact positive_canonical_mem_nans width inputs h

theorem canonicalClosed_singleton (width : Nat) (value : fN)
    (h : isNaN value = false) : CanonicalClosed width [value] := by
  rintro ⟨choice, hc, hn⟩
  simp only [List.mem_singleton] at hc
  subst choice
  simp [h] at hn

theorem canonical_positive (width : Nat) (hw : width = 32 ∨ width = 64) :
    0 < canon_ width := by
  rcases hw with rfl | rfl
  · exact canonical_positive_32
  · exact canonical_positive_64

theorem withSign_INF_noNaN (sign : Bool) : isNaN (withSign sign .INF) = false := by
  cases sign <;> rfl

theorem withSign_zero_noNaN (sign : Bool) : isNaN (withSign sign (.SUBNORM 0)) = false := by
  cases sign <;> rfl

theorem canonicalClosed_add (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fadd_ width a b) := by
  unfold fadd_
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · apply canonicalClosed_singleton
    simp_all
  · apply canonicalClosed_singleton
    simp_all
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_sub (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fsub_ width a b) := by
  unfold fsub_
  split
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_add width hw _ _

theorem canonicalClosed_mul (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fmul_ width a b) := by
  unfold fmul_
  split_ifs
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (withSign_INF_noNaN _)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_div (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (withSign_INF_noNaN _)
  · exact canonicalClosed_singleton _ _ (withSign_zero_noNaN _)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_sqrt (width : Nat) (hw : width = 32 ∨ width = 64) (a : fN) :
    CanonicalClosed width (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (roundSqrt_noNaN width hw _)

theorem canonicalClosed_integral (width : Nat) (hw : width = 32 ∨ width = 64)
    (op : Rat → Int) (a : fN) : CanonicalClosed width (integral op width a) := by
  unfold integral
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_convert (source target : Nat) (hw : target = 32 ∨ target = 64)
    (sign : sx) (a : iN) : CanonicalClosed target [convert__ source target sign a] := by
  exact canonicalClosed_singleton _ _ (round_noNaN target hw _ _)

theorem canonicalClosed_demote (source target : Nat) (hw : target = 32 ∨ target = 64)
    (a : fN) : CanonicalClosed target (demote__ source target a) := by
  unfold demote__
  split_ifs with hn
  · intro _; exact positive_canonical_mem target
  · intro _; exact positive_canonical_mem_arithmetic target (canonical_positive target hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (round_noNaN target hw _ _)

end SpecExt.Builtins.Float
