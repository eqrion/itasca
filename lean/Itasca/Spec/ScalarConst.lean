import Itasca.Support.TypeTranslation

/-!
# `i64`, `f32` and `f64` constants in SpecTec

Encodes extracted `i64` values and `f32`/`f64` bit patterns as SpecTec `*.const` instructions.
`i64_wf`, `f32_wf`, `f64_wf` show well-formedness, and the `*_typed` and `*_framed` theorems give
`Instr_ok` and `Instrs_ok` typing.
-/

open Aeneas Aeneas.Std

namespace Itasca.ScalarConst

/-- The SpecTec `i64.const` instruction for `value`, using its unsigned 64-bit bit pattern. -/
def i64 (value : I64) : instr :=
  .CONST .I64 (.mk_num__0 .I64 (.mk_uN (value.val % 18446744073709551616).toNat))

/-- The encoded `i64.const` instruction is well-formed. -/
theorem i64_wf (value : I64) : wf_instr (i64 value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I64 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 18446744073709551616)
  have hnonneg := Int.emod_nonneg value.val (by decide : (18446744073709551616 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

/-- The SpecTec float with the given IEEE field widths and bit pattern. Fields are translated
directly, so the sign of zero and NaN payloads are kept. -/
def floatValue (fractionBits exponentBits bits : Nat) : fN :=
  let fraction := bits % 2 ^ fractionBits
  let exponent := bits / 2 ^ fractionBits % 2 ^ exponentBits
  let magnitude :=
    if exponent = 0 then fNmag.SUBNORM fraction
    else if exponent = 2 ^ exponentBits - 1 then
      if fraction = 0 then fNmag.INF else fNmag.NAN fraction
    else fNmag.NORM fraction ((exponent : Int) - (2 ^ (exponentBits - 1) - 1 : Nat))
  if bits < 2 ^ (fractionBits + exponentBits) then .POS magnitude else .NEG magnitude

/-- The SpecTec `f32.const` instruction for the bit pattern `bits`. -/
def f32 (bits : U32) : instr := .CONST .F32 (.mk_num__1 .F32 (floatValue 23 8 bits.val))
/-- The SpecTec `f64.const` instruction for the bit pattern `bits`. -/
def f64 (bits : U64) : instr := .CONST .F64 (.mk_num__1 .F64 (floatValue 52 11 bits.val))

theorem floatValue_wf32 (bits : Nat) : wf_fN 32 (floatValue 23 8 bits) := by
  have hm : bits % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have he : bits / 2 ^ 23 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hmag : wf_fNmag 32
      (if bits / 2 ^ 23 % 2 ^ 8 = 0 then .SUBNORM (bits % 2 ^ 23)
       else if bits / 2 ^ 23 % 2 ^ 8 = 2 ^ 8 - 1 then
         if bits % 2 ^ 23 = 0 then .INF else .NAN (bits % 2 ^ 23)
       else .NORM (bits % 2 ^ 23) ((bits / 2 ^ 23 % 2 ^ 8 : Nat) - (2 ^ (8 - 1) - 1 : Nat) : Int)) := by
    generalize hmdef : bits % 2 ^ 23 = fraction at *
    generalize hedef : bits / 2 ^ 23 % 2 ^ 8 = exponent at *
    split
    · apply wf_fNmag.fNmag_case_1 32 (2 - 2 ^ (8 - 1))
      exact ⟨hm, by decide⟩
    · split
      · split
        · exact .fNmag_case_2 _
        · apply wf_fNmag.fNmag_case_3
          exact ⟨Nat.one_le_iff_ne_zero.mpr (by assumption), hm⟩
      · apply wf_fNmag.fNmag_case_0
        refine ⟨hm, ?_, ?_⟩ <;> norm_num [E, expon, Int.toNat] at * <;> omega
  unfold floatValue
  split
  · exact .fN_case_0 _ _ hmag
  · exact .fN_case_1 _ _ hmag

/-- The encoded `f32.const` instruction is well-formed. -/
theorem f32_wf (bits : U32) : wf_instr (f32 bits) := by
  apply wf_instr.instr_case_13
  exact wf_num_.num__case_1 _ .F32 _ (floatValue_wf32 bits.val) rfl

theorem floatValue_wf64 (bits : Nat) : wf_fN 64 (floatValue 52 11 bits) := by
  have hm : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have he : bits / 2 ^ 52 % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hmag : wf_fNmag 64
      (if bits / 2 ^ 52 % 2 ^ 11 = 0 then .SUBNORM (bits % 2 ^ 52)
       else if bits / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1 then
         if bits % 2 ^ 52 = 0 then .INF else .NAN (bits % 2 ^ 52)
       else .NORM (bits % 2 ^ 52) ((bits / 2 ^ 52 % 2 ^ 11 : Nat) - (2 ^ (11 - 1) - 1 : Nat) : Int)) := by
    generalize hmdef : bits % 2 ^ 52 = fraction at *
    generalize hedef : bits / 2 ^ 52 % 2 ^ 11 = exponent at *
    split
    · apply wf_fNmag.fNmag_case_1 64 (2 - 2 ^ (11 - 1))
      exact ⟨hm, by decide⟩
    · split
      · split
        · exact .fNmag_case_2 _
        · apply wf_fNmag.fNmag_case_3
          exact ⟨Nat.one_le_iff_ne_zero.mpr (by assumption), hm⟩
      · apply wf_fNmag.fNmag_case_0
        refine ⟨hm, ?_, ?_⟩ <;> norm_num [E, expon, Int.toNat] at * <;> omega
  unfold floatValue
  split
  · exact .fN_case_0 _ _ hmag
  · exact .fN_case_1 _ _ hmag

/-- The encoded `f64.const` instruction is well-formed. -/
theorem f64_wf (bits : U64) : wf_instr (f64 bits) := by
  apply wf_instr.instr_case_13
  exact wf_num_.num__case_1 _ .F64 _ (floatValue_wf64 bits.val) rfl

/-- The encoded `i64.const` instruction has type `[] -> [i64]` under `Instr_ok`. -/
theorem i64_typed (C : context) (hC : wf_context C) (value : I64) :
    Instr_ok C (i64 value) (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
  .const C .I64 _ hC (i64_wf value)

/-- The encoded `i64.const` instruction is typed under `Instrs_ok` on top of any stack `ts`. -/
theorem i64_framed (C : context) (hC : wf_context C) (value : I64) (ts : List valtype) :
    Instrs_ok C [i64 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I64]))) := by
  simpa using Instrs_ok.frame C [i64 value] ts [] [.I64]
    (.instr C _ [] [.I64] (i64_typed C hC value) hC (i64_wf value))
    hC (by simpa [Forall] using i64_wf value)

/-- The encoded `f32.const` instruction has type `[] -> [f32]` under `Instr_ok`. -/
theorem f32_typed (C : context) (hC : wf_context C) (value : U32) :
    Instr_ok C (f32 value) (.mk_functype (.mk_list []) (.mk_list [.F32])) :=
  .const C .F32 _ hC (f32_wf value)

/-- The encoded `f32.const` instruction is typed under `Instrs_ok` on top of any stack `ts`. -/
theorem f32_framed (C : context) (hC : wf_context C) (value : U32) (ts : List valtype) :
    Instrs_ok C [f32 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.F32]))) := by
  simpa using Instrs_ok.frame C [f32 value] ts [] [.F32]
    (.instr C _ [] [.F32] (f32_typed C hC value) hC (f32_wf value))
    hC (by simpa [Forall] using f32_wf value)

/-- The encoded `f64.const` instruction has type `[] -> [f64]` under `Instr_ok`. -/
theorem f64_typed (C : context) (hC : wf_context C) (value : U64) :
    Instr_ok C (f64 value) (.mk_functype (.mk_list []) (.mk_list [.F64])) :=
  .const C .F64 _ hC (f64_wf value)

/-- The encoded `f64.const` instruction is typed under `Instrs_ok` on top of any stack `ts`. -/
theorem f64_framed (C : context) (hC : wf_context C) (value : U64) (ts : List valtype) :
    Instrs_ok C [f64 value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.F64]))) := by
  simpa using Instrs_ok.frame C [f64 value] ts [] [.F64]
    (.instr C _ [] [.F64] (f64_typed C hC value) hC (f64_wf value))
    hC (by simpa [Forall] using f64_wf value)

end Itasca.ScalarConst
