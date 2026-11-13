import Itasca.Support.Result

/-!
Sections, each formerly its own module: Instr, ScalarConst, TypingInversion.
-/

/-! ## Instr -/

section

/-!
# `i32.const` and label indices in SpecTec

`Spec.i32Const` encodes an extracted `i32` as a SpecTec `i32.const` instruction by its unsigned
bit pattern, with well-formedness (`i32Const_wf`) and typing (`i32Const_typed`, `i32Const_framed`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Spec

/-- The SpecTec `i32.const` instruction for `value`, using its unsigned 32-bit bit pattern. -/
def i32Const (value : I32) : instr :=
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value.val % 4294967296).toNat))

/-- The encoded `i32.const` instruction is well-formed. -/
theorem i32Const_wf (value : I32) : wf_instr (i32Const value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I32 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
  have hnonneg := Int.emod_nonneg value.val (by decide : (4294967296 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

/-- A `u32` label index is a well-formed 32-bit `uN`. -/
theorem label_wf (depth : U32) : wf_uN 32 (.mk_uN depth.val) := by
  apply wf_uN.uN_case_0
  have h := depth.hmax
  norm_num at h ⊢
  omega

/-- The encoded `i32.const` instruction has type `[] -> [i32]` under `Instr_ok`. -/
theorem i32Const_typed (C : context) (hC : wf_context C) (value : I32) :
    Instr_ok C (i32Const value) (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
  .const C .I32 _ hC (i32Const_wf value)

/-- The encoded `i32.const` instruction is typed under `Instrs_ok` on top of any stack `ts`. -/
theorem i32Const_framed (C : context) (hC : wf_context C) (value : I32) (ts : List valtype) :
    Instrs_ok C [i32Const value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I32]))) := by
  simpa using Instrs_ok.frame C [i32Const value] ts [] [.I32]
    (.instr C _ [] [.I32] (i32Const_typed C hC value) hC (i32Const_wf value))
    hC (by simpa [Forall] using i32Const_wf value)

end Itasca.Spec

end

/-! ## ScalarConst -/

section

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

end

/-! ## TypingInversion -/

section

/-!
# Inversion of declarative sequence typing

Facts about the generated `Instrs_ok` that completeness proofs need because the generated rules
include subsumption (`sub`), framing (`frame`) and sequencing (`seq`) at every level. The main
results are `singleton` (a one-instruction derivation is one `Instr_ok` rule plus a frame and
subtyping), `split` and `head_normal` (a sequence can be cut at any instruction boundary), and the
subtyping lemmas `result_sub_iff`, `result_sub_trans` and `empty_iff`.
-/

namespace Itasca.DeclarativeComplete

/-- `Resulttype_sub` is the pointwise `Valtype_sub` relation on lists: its length side condition
and zip-based premise together say exactly that. -/
theorem result_sub_iff {a b : List valtype} :
    Resulttype_sub (.mk_list a) (.mk_list b) ↔ List.Forall₂ Valtype_sub a b := by
  constructor
  · intro h
    cases h with
    | mk_Resulttype_sub _ _ hlen hp =>
      rw [List.forall₂_iff_zip]
      exact ⟨hlen, fun hmem => hp _ hmem⟩
  · intro h
    rw [List.forall₂_iff_zip] at h
    exact .mk_Resulttype_sub _ _ h.1 (fun ⟨a, b⟩ hmem => h.2 hmem)

/-- `Valtype_sub` is transitive. -/
theorem value_sub_trans {a b c : valtype}
    (hab : Valtype_sub a b) (hbc : Valtype_sub b c) : Valtype_sub a c := by
  cases hab with
  | refl => exact hbc
  | bot => exact .bot _

/-- `Resulttype_sub` is reflexive. -/
theorem result_sub_refl (a : List valtype) :
    Resulttype_sub (.mk_list a) (.mk_list a) := by
  apply result_sub_iff.mpr
  induction a with
  | nil => exact .nil
  | cons a tail ih => exact .cons (.refl a) ih

/-- `Resulttype_sub` is transitive. -/
theorem result_sub_trans {a b c : List valtype}
    (hab : Resulttype_sub (.mk_list a) (.mk_list b))
    (hbc : Resulttype_sub (.mk_list b) (.mk_list c)) :
    Resulttype_sub (.mk_list a) (.mk_list c) := by
  apply result_sub_iff.mpr
  have hab' := result_sub_iff.mp hab
  have hbc' := result_sub_iff.mp hbc
  clear hab hbc
  induction hab' generalizing c with
  | nil => cases hbc'; exact .nil
  | cons h hs ih =>
    cases hbc' with
    | cons h' hs' => exact .cons (value_sub_trans h h') (ih hs')

/-- `Resulttype_sub` is preserved by concatenation. -/
theorem result_sub_append {a b c d : List valtype}
    (hab : Resulttype_sub (.mk_list a) (.mk_list b))
    (hcd : Resulttype_sub (.mk_list c) (.mk_list d)) :
    Resulttype_sub (.mk_list (a ++ c)) (.mk_list (b ++ d)) :=
  result_sub_iff.mpr (List.rel_append (result_sub_iff.mp hab) (result_sub_iff.mp hcd))

/-- `Resulttype_sub` relates lists of equal length. -/
theorem result_sub_length {a b : List valtype}
    (h : Resulttype_sub (.mk_list a) (.mk_list b)) : a.length = b.length :=
  (result_sub_iff.mp h).length_eq

/-- A derivable `Instrs_ok` judgment has a well-formed context and well-formed instructions. -/
theorem wellFormed {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) : wf_context C ∧ Forall wf_instr ops := by
  cases h <;> simp_all [Forall, or_imp]

private theorem empty_sub_aux {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (he : ops = []) :
    match ft with | .mk_functype a b => Resulttype_sub a b := by
  revert he
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) <;>
    try (intros; trivial)
  case empty => intro _; exact result_sub_refl []
  case seq C xs ys a b mid hx hy hC hwx hwy ihx ihy =>
    intro he
    have hh := List.append_eq_nil_iff.mp he
    exact result_sub_trans (ihx hh.1) (ihy hh.2)
  case sub C ops a' b' a b h hin hout hC hw ih =>
    intro he
    exact result_sub_trans hin (result_sub_trans (ih he) hout)
  case frame C ops front a b h hC hw ih =>
    intro he
    exact result_sub_append (result_sub_refl front) (ih he)

/-- An empty sequence is typed only at a subtype pair of stacks. -/
theorem empty_sub {C : context} {a b : List valtype}
    (h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b))) :
    Resulttype_sub (.mk_list a) (.mk_list b) := empty_sub_aux h rfl

/-- An empty sequence has type `a -> b` exactly when the context is well-formed and `a` is a
subtype of `b`. -/
theorem empty_iff {C : context} {a b : List valtype} :
    Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b)) ↔
      wf_context C ∧ Resulttype_sub (.mk_list a) (.mk_list b) := by
  constructor
  · intro h
    exact ⟨(wellFormed h).1, empty_sub h⟩
  · rintro ⟨hC, hs⟩
    have h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list a)) := by
      simpa using Instrs_ok.frame C [] a [] [] (.empty C hC) hC (by simp [Forall])
    exact .sub C [] a b a a h (result_sub_refl a) hs hC (by simp [Forall])

private theorem append_singleton {α : Type} {xs ys : List α} {x : α}
    (h : xs ++ ys = [x]) :
    (xs = [] ∧ ys = [x]) ∨ (xs = [x] ∧ ys = []) := by
  cases xs with
  | nil => exact Or.inl ⟨rfl, by simpa using h⟩
  | cons y rest =>
    have hh : y = x ∧ rest ++ ys = [] := by simpa using h
    have hn := List.append_eq_nil_iff.mp hh.2
    exact Or.inr ⟨by simp [hh.1, hn.1], hn.2⟩

private theorem singleton_aux {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) : ∀ op, ops = [op] →
    match ft with
    | .mk_functype a b => ∃ front ins outs,
        Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
        Resulttype_sub a (.mk_list (front ++ ins)) ∧
        Resulttype_sub (.mk_list (front ++ outs)) b := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) <;>
    try (intros; trivial)
  case instr C op a b hop hC hw ih =>
    intro op' he
    have heq : op = op' := by simpa using he
    subst op'
    exact ⟨[], a, b, hop, result_sub_refl a, result_sub_refl b⟩
  case seq C xs ys a b mid hx hy hC hwx hwy ihx ihy =>
    intro op he
    rcases append_singleton he with ⟨hex, hey⟩ | ⟨hex, hey⟩
    · obtain ⟨front, ins, outs, hop, hin, hout⟩ := ihy op hey
      exact ⟨front, ins, outs, hop, result_sub_trans (empty_sub_aux hx hex) hin, hout⟩
    · obtain ⟨front, ins, outs, hop, hin, hout⟩ := ihx op hex
      exact ⟨front, ins, outs, hop, hin, result_sub_trans hout (empty_sub_aux hy hey)⟩
  case sub C ops a' b' a b h hin hout hC hw ih =>
    intro op he
    obtain ⟨front, ins, outs, hop, hni, hno⟩ := ih op he
    exact ⟨front, ins, outs, hop, result_sub_trans hin hni, result_sub_trans hno hout⟩
  case frame C ops frame a b h hC hw ih =>
    intro op he
    obtain ⟨front, ins, outs, hop, hin, hout⟩ := ih op he
    refine ⟨frame ++ front, ins, outs, hop, ?_, ?_⟩
    · simpa [List.append_assoc] using result_sub_append (result_sub_refl frame) hin
    · simpa [List.append_assoc] using result_sub_append (result_sub_refl frame) hout

/-- Every singleton derivation is one primitive `Instr_ok` rule, with a common stack frame and
input and output subtyping. Nested sequence, frame and subsumption rules add nothing else. -/
theorem singleton {C : context} {op : instr} {a b : List valtype}
    (h : Instrs_ok C [op] (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Resulttype_sub (.mk_list a) (.mk_list (front ++ ins)) ∧
      Resulttype_sub (.mk_list (front ++ outs)) (.mk_list b) :=
  singleton_aux h op rfl

/-- Typings of two sequences with matching middle stack compose under `Instrs_ok`. -/
theorem append {C : context} {xs ys : List instr} {a mid b : List valtype}
    (hx : Instrs_ok C xs (.mk_functype (.mk_list a) (.mk_list mid)))
    (hy : Instrs_ok C ys (.mk_functype (.mk_list mid) (.mk_list b))) :
    Instrs_ok C (xs ++ ys) (.mk_functype (.mk_list a) (.mk_list b)) :=
  .seq C xs ys a b mid hx hy (wellFormed hx).1 (wellFormed hx).2 (wellFormed hy).2

/-- The input stack of a typed sequence can be replaced by a subtype. -/
theorem narrow_input {C : context} {ops : List instr} {a a' b : List valtype}
    (h : Instrs_ok C ops (.mk_functype (.mk_list a) (.mk_list b)))
    (hs : Resulttype_sub (.mk_list a') (.mk_list a)) :
    Instrs_ok C ops (.mk_functype (.mk_list a') (.mk_list b)) :=
  .sub C ops a' b a b h hs (result_sub_refl b) (wellFormed h).1 (wellFormed h).2

/-- The output stack of a typed sequence can be replaced by a supertype. -/
theorem widen_output {C : context} {ops : List instr} {a b b' : List valtype}
    (h : Instrs_ok C ops (.mk_functype (.mk_list a) (.mk_list b)))
    (hs : Resulttype_sub (.mk_list b) (.mk_list b')) :
    Instrs_ok C ops (.mk_functype (.mk_list a) (.mk_list b')) :=
  .sub C ops a b' a b h (result_sub_refl a) hs (wellFormed h).1 (wellFormed h).2

private theorem split_aux {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) : ∀ xs ys, ops = xs ++ ys →
    match ft with
    | .mk_functype a b => ∃ mid : List valtype,
        Instrs_ok C xs (.mk_functype a (.mk_list mid)) ∧
        Instrs_ok C ys (.mk_functype (.mk_list mid) b) := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True) <;>
    try (intros; trivial)
  case empty C hC =>
    intro xs ys he
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact ⟨[], .empty C hC, .empty C hC⟩
  case instr C op a b hop hC hw ih =>
    intro xs ys he
    rcases append_singleton he.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a, empty_iff.mpr ⟨hC, result_sub_refl a⟩, .instr C op a b hop hC hw⟩
    · exact ⟨b, .instr C op a b hop hC hw, empty_iff.mpr ⟨hC, result_sub_refl b⟩⟩
  case seq C left right a b oldmid hl hr hC hwl hwr ihl ihr =>
    intro xs ys he
    rcases List.append_eq_append_iff.mp he with ⟨extra, hx, hy⟩ | ⟨extra, hx, hy⟩
    · obtain ⟨mid, hpre, hpost⟩ := ihr extra ys hy
      exact ⟨mid, hx ▸ append hl hpre, hpost⟩
    · obtain ⟨mid, hpre, hpost⟩ := ihl xs extra hx
      exact ⟨mid, hpre, hy ▸ append hpost hr⟩
  case sub C ops a' b' a b h hin hout hC hw ih =>
    intro xs ys he
    obtain ⟨mid, hpre, hpost⟩ := ih xs ys he
    exact ⟨mid, narrow_input hpre hin, widen_output hpost hout⟩
  case frame C ops front a b h hC hw ih =>
    intro xs ys he
    obtain ⟨mid, hpre, hpost⟩ := ih xs ys he
    exact ⟨front ++ mid,
      .frame C xs front a mid hpre hC (wellFormed hpre).2,
      .frame C ys front mid b hpost hC (wellFormed hpost).2⟩

/-- Sequence typing splits at any syntactic instruction boundary, across arbitrarily nested
subsumption and framing derivations. -/
theorem split {C : context} {xs ys : List instr} {a b : List valtype}
    (h : Instrs_ok C (xs ++ ys) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ mid, Instrs_ok C xs (.mk_functype (.mk_list a) (.mk_list mid)) ∧
      Instrs_ok C ys (.mk_functype (.mk_list mid) (.mk_list b)) :=
  split_aux h xs ys rfl

/-- A typed non-empty sequence splits into its first instruction and the rest. -/
theorem head {C : context} {op : instr} {ops : List instr} {a b : List valtype}
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ mid, Instrs_ok C [op] (.mk_functype (.mk_list a) (.mk_list mid)) ∧
      Instrs_ok C ops (.mk_functype (.mk_list mid) (.mk_list b)) :=
  split (xs := [op]) h

/-- A typed non-empty sequence decomposes into the first instruction's primitive rule, a frame, and
the typing of the remaining instructions, with the output widening absorbed into the remainder. -/
theorem head_normal {C : context} {op : instr} {ops : List instr} {a b : List valtype}
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Resulttype_sub (.mk_list a) (.mk_list (front ++ ins)) ∧
      Instrs_ok C ops (.mk_functype (.mk_list (front ++ outs)) (.mk_list b)) := by
  obtain ⟨mid, hfirst, hrest⟩ := head h
  obtain ⟨front, ins, outs, hop, hin, hout⟩ := singleton hfirst
  exact ⟨front, ins, outs, hop, hin, narrow_input hrest hout⟩

end Itasca.DeclarativeComplete

end
