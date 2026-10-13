import Itasca.Handler.Sequence

open Aeneas Aeneas.Std

namespace Itasca.Frames

private theorem accepts_concrete (rs : List types.ValueType) (ts : List valtype) :
    List.Forall₂ Sequence.Accepts (rs.map code.StackType.Val) ts ↔
      ts = rs.map Translate.valueType := by
  induction rs generalizing ts with
  | nil => simp
  | cons r rs ih =>
    cases ts <;> simp [Sequence.Accepts, ih]

/-- Appended concrete operands have a unique suffix in every stack realization. -/
theorem realizes_append_concrete (poly : Bool) (vals : List code.StackType)
    (rs : List types.ValueType) (ts : List valtype) :
    Sequence.Realizes poly (vals ++ rs.map code.StackType.Val) ts ↔
      ∃ pre, Sequence.Realizes poly vals pre ∧ ts = pre ++ rs.map Translate.valueType := by
  constructor
  · rintro ⟨front, suffix, hf, hs, rfl⟩
    have ht := List.forall₂_take vals.length hs
    have hd := List.forall₂_drop vals.length hs
    simp only [List.take_left, List.drop_left] at ht hd
    have heq := (accepts_concrete rs _).mp hd
    refine ⟨front ++ suffix.take vals.length, ⟨front, _, hf, ht, rfl⟩, ?_⟩
    rw [← heq, List.append_assoc, List.take_append_drop]
  · rintro ⟨pre, ⟨front, suffix, hf, hs, rfl⟩, rfl⟩
    exact ⟨front, suffix ++ rs.map Translate.valueType, hf,
      List.rel_append hs ((accepts_concrete rs _).mpr rfl), List.append_assoc ..⟩

/-- A suspended prefix retains the arguments consumed when its child was entered.
For an if these are `[I32]`; blocks and loops have no input arguments in Wasm 1.0. -/
structure ResumePrefix (C : context) (ops : List instr) (poly : Bool)
    (vals : List code.StackType) (inputs : List valtype) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list (ts ++ inputs)))

theorem ResumePrefix.of_prefix {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : Sequence.TypedPrefix C ops poly vals) :
    ResumePrefix C ops poly vals [] := by
  exact ⟨h.wellFormed, by simpa using h.typed⟩

theorem ResumePrefix.after_pop {C : context} {ops : List instr} {poly : Bool}
    {before after : List code.StackType} {inputs : List valtype}
    (h : Sequence.TypedPrefix C ops poly before)
    (hpop : ∀ ts, Sequence.Realizes poly after ts →
      Sequence.Realizes poly before (ts ++ inputs)) :
    ResumePrefix C ops poly after inputs :=
  ⟨h.wellFormed, fun ts ht => h.typed _ (hpop ts ht)⟩

/-- Completing a child restores its result operands and resumes its parent prefix. -/
theorem ResumePrefix.finish {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} {inputs : List valtype}
    (h : ResumePrefix C ops poly vals inputs) (hC : wf_context C)
    (op : instr) (rs : List types.ValueType) (hwf : wf_instr op)
    (hop : Instr_ok C op
      (.mk_functype (.mk_list inputs) (.mk_list (rs.map Translate.valueType)))) :
    Sequence.TypedPrefix C (ops ++ [op]) poly (vals ++ rs.map code.StackType.Val) := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (realizes_append_concrete poly vals rs ts).mp ht
    exact .seq C ops [op] [] (pre ++ rs.map Translate.valueType) (pre ++ inputs)
      (h.typed pre hp)
      (.frame C [op] pre inputs (rs.map Translate.valueType)
        (.instr C op inputs _ hop hC hwf) hC (by simpa [Forall] using hwf))
      hC h.wellFormed (by simpa [Forall] using hwf)

end Itasca.Frames
