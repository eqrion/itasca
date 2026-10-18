import SpecExt.Builtins.Float.Convert

/-! Kernel-checked facts about the specification's NaN choices. In particular,
a wrapper that canonicalizes a permitted arithmetic NaN remains in the result
set; it need not reproduce an implementation-selected payload or sign. -/

namespace SpecExt.Builtins.Float

theorem positive_canonical_mem (width : Nat) :
    fN.POS (.NAN (canon_ width)) ∈ canonicalNaNs width := by
  simp [canonicalNaNs]

theorem negative_canonical_mem (width : Nat) :
    fN.NEG (.NAN (canon_ width)) ∈ canonicalNaNs width := by
  simp [canonicalNaNs]

theorem positive_canonical_mem_arithmetic (width : Nat) (h : 0 < canon_ width) :
    fN.POS (.NAN (canon_ width)) ∈ arithmeticNaNs width := by
  apply List.mem_flatMap.mpr
  exact ⟨0, List.mem_range.mpr h, by simp⟩

theorem negative_canonical_mem_arithmetic (width : Nat) (h : 0 < canon_ width) :
    fN.NEG (.NAN (canon_ width)) ∈ arithmeticNaNs width := by
  apply List.mem_flatMap.mpr
  exact ⟨0, List.mem_range.mpr h, by simp⟩

theorem positive_canonical_mem_nans (width : Nat) (inputs : List fN)
    (h : 0 < canon_ width) : fN.POS (.NAN (canon_ width)) ∈ nans width inputs := by
  unfold nans
  split
  · exact positive_canonical_mem width
  · exact positive_canonical_mem_arithmetic width h

theorem canonical_positive_32 : 0 < canon_ 32 := by decide
theorem canonical_positive_64 : 0 < canon_ 64 := by decide

theorem abs_preserves_payload (width payload : Nat) (sign : Bool) :
    fabs_ width (withSign sign (.NAN payload)) = [.POS (.NAN payload)] := by
  cases sign <;> rfl

theorem copysign_preserves_magnitude (width : Nat) (mag : fNmag) (a b : Bool) :
    fcopysign_ width (withSign a mag) (withSign b (.SUBNORM 0)) = [withSign b mag] := by
  cases a <;> cases b <;> rfl

end SpecExt.Builtins.Float
