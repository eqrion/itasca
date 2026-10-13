import Itasca.Support.TypeTranslation

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
