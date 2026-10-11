import Itasca.Body.Sequence

namespace Itasca.DeclarativeComplete

/-- The generated zip-based relation has its length side condition built into
`Resulttype_sub`; together they are the ordinary pointwise list relation. -/
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

theorem value_sub_trans {a b c : valtype}
    (hab : Valtype_sub a b) (hbc : Valtype_sub b c) : Valtype_sub a c := by
  cases hab with
  | refl => exact hbc
  | bot => exact .bot _

theorem result_sub_refl (a : List valtype) :
    Resulttype_sub (.mk_list a) (.mk_list a) := by
  apply result_sub_iff.mpr
  induction a with
  | nil => exact .nil
  | cons a tail ih => exact .cons (.refl a) ih

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

theorem result_sub_append {a b c d : List valtype}
    (hab : Resulttype_sub (.mk_list a) (.mk_list b))
    (hcd : Resulttype_sub (.mk_list c) (.mk_list d)) :
    Resulttype_sub (.mk_list (a ++ c)) (.mk_list (b ++ d)) :=
  result_sub_iff.mpr (List.rel_append (result_sub_iff.mp hab) (result_sub_iff.mp hcd))

theorem result_sub_length {a b : List valtype}
    (h : Resulttype_sub (.mk_list a) (.mk_list b)) : a.length = b.length :=
  (result_sub_iff.mp h).length_eq

theorem accepts_mono {t : code.StackType} {a b : valtype}
    (h : Sequence.Accepts t a) (hs : Valtype_sub a b) : Sequence.Accepts t b := by
  cases t with
  | Bot => trivial
  | Val t =>
    cases hs with
    | refl => exact h
    | bot => cases t <;> simp [Sequence.Accepts, Translate.valueType] at h

theorem accepts_list_mono {vals : List code.StackType} {a b : List valtype}
    (h : List.Forall₂ Sequence.Accepts vals a) (hs : List.Forall₂ Valtype_sub a b) :
    List.Forall₂ Sequence.Accepts vals b := by
  induction h generalizing b with
  | nil => cases hs; exact .nil
  | cons h ht ih =>
    cases hs with
    | cons hs ht' => exact .cons (accepts_mono h hs) (ih ht')

/-- Widening a declarative stack never invalidates its concrete/Bot realization. -/
theorem realizes_mono {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (h : Sequence.Realizes poly vals a)
    (hs : Resulttype_sub (.mk_list a) (.mk_list b)) : Sequence.Realizes poly vals b := by
  obtain ⟨front, suffix, hf, hv, rfl⟩ := h
  have hs := result_sub_iff.mp hs
  have hf' := List.forall₂_take front.length hs
  have ht' := List.forall₂_drop front.length hs
  simp only [List.take_left, List.drop_left] at hf' ht'
  refine ⟨b.take front.length, b.drop front.length, ?_, ?_, (List.take_append_drop _ _).symm⟩
  · intro hp
    simp [hf hp]
  · exact accepts_list_mono hv ht'

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

theorem empty_sub {C : context} {a b : List valtype}
    (h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b))) :
    Resulttype_sub (.mk_list a) (.mk_list b) := empty_sub_aux h rfl

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

/-- Every singleton derivation is one primitive instruction rule, with one
common stack frame and input/output subtyping. Nested sequence, frame, and
subsumption rules introduce no other possibilities. -/
theorem singleton {C : context} {op : instr} {a b : List valtype}
    (h : Instrs_ok C [op] (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Resulttype_sub (.mk_list a) (.mk_list (front ++ ins)) ∧
      Resulttype_sub (.mk_list (front ++ outs)) (.mk_list b) :=
  singleton_aux h op rfl

theorem append {C : context} {xs ys : List instr} {a mid b : List valtype}
    (hx : Instrs_ok C xs (.mk_functype (.mk_list a) (.mk_list mid)))
    (hy : Instrs_ok C ys (.mk_functype (.mk_list mid) (.mk_list b))) :
    Instrs_ok C (xs ++ ys) (.mk_functype (.mk_list a) (.mk_list b)) :=
  .seq C xs ys a b mid hx hy (wellFormed hx).1 (wellFormed hx).2 (wellFormed hy).2

theorem narrow_input {C : context} {ops : List instr} {a a' b : List valtype}
    (h : Instrs_ok C ops (.mk_functype (.mk_list a) (.mk_list b)))
    (hs : Resulttype_sub (.mk_list a') (.mk_list a)) :
    Instrs_ok C ops (.mk_functype (.mk_list a') (.mk_list b)) :=
  .sub C ops a' b a b h hs (result_sub_refl b) (wellFormed h).1 (wellFormed h).2

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

/-- Sequence typing can be split at any syntactic instruction boundary,
including across arbitrarily nested subsumption and framing derivations. -/
theorem split {C : context} {xs ys : List instr} {a b : List valtype}
    (h : Instrs_ok C (xs ++ ys) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ mid, Instrs_ok C xs (.mk_functype (.mk_list a) (.mk_list mid)) ∧
      Instrs_ok C ys (.mk_functype (.mk_list mid) (.mk_list b)) :=
  split_aux h xs ys rfl

theorem head {C : context} {op : instr} {ops : List instr} {a b : List valtype}
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ mid, Instrs_ok C [op] (.mk_functype (.mk_list a) (.mk_list mid)) ∧
      Instrs_ok C ops (.mk_functype (.mk_list mid) (.mk_list b)) :=
  split (xs := [op]) h

/-- Normalize the next primitive rule and absorb its output widening into the
remaining sequence. This is a declarative residual-typing decomposition. -/
theorem head_normal {C : context} {op : instr} {ops : List instr} {a b : List valtype}
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Resulttype_sub (.mk_list a) (.mk_list (front ++ ins)) ∧
      Instrs_ok C ops (.mk_functype (.mk_list (front ++ outs)) (.mk_list b)) := by
  obtain ⟨mid, hfirst, hrest⟩ := head h
  obtain ⟨front, ins, outs, hop, hin, hout⟩ := singleton hfirst
  exact ⟨front, ins, outs, hop, hin, narrow_input hrest hout⟩

/-- A realizable input stack for a typed nonempty residual program realizes
the primitive head's framed input; its framed output types the residual tail.
No execution or acceptance premise is involved. -/
theorem head_realizes {C : context} {op : instr} {ops : List instr}
    {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Sequence.Realizes poly vals (front ++ ins) ∧
      Instrs_ok C ops (.mk_functype (.mk_list (front ++ outs)) (.mk_list b)) := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  exact ⟨front, ins, outs, hop, realizes_mono hr hin, hrest⟩

theorem empty_realizes {C : context} {poly : Bool} {vals : List code.StackType}
    {a b : List valtype} (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b))) :
    Sequence.Realizes poly vals b := realizes_mono hr (empty_sub h)

end Itasca.DeclarativeComplete
