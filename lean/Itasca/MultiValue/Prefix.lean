import Itasca.Body.WasmFrames

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- A frame starts with its parameter vector. Function bodies use the empty
vector because function parameters are locals, not initial operands. -/
structure TypedPrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list ts))

theorem TypedPrefix.start (C : context) (hC : wf_context C) (inputs : List types.ValueType) :
    TypedPrefix C (inputs.map Translate.valueType) [] false
      (inputs.map code.StackType.Val) := by
  constructor
  · simp [Forall]
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Frames.realizes_append_concrete false [] inputs ts).mp
      (by simpa using ht)
    have he := (Sequence.realizes_empty pre).mp hp
    subst pre
    simpa using Instrs_ok.frame C [] (inputs.map Translate.valueType) [] []
      (.empty C hC) hC (by simp [Forall])

theorem TypedPrefix.append {C inputs ops poly poly' vals vals'}
    (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C)
    (op : instr) (hwf : wf_instr op)
    (hstep : ∀ out, Sequence.Realizes poly' vals' out →
      ∃ before, Sequence.Realizes poly vals before ∧
        Instrs_ok C [op] (.mk_functype (.mk_list before) (.mk_list out))) :
    TypedPrefix C inputs (ops ++ [op]) poly' vals' := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro out hout
    obtain ⟨before, hin, hop⟩ := hstep out hout
    exact .seq C ops [op] inputs out before (h.typed before hin) hop hC
      h.wellFormed (by simpa [Forall] using hwf)

/-- A suspended parent remembers the child's parameters and, for if, its i32
condition, even though those operands have been popped from the physical stack. -/
structure ResumePrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) (args : List valtype) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list (ts ++ args)))

theorem ResumePrefix.after_pop {C inputs ops poly before after args}
    (h : TypedPrefix C inputs ops poly before)
    (hpop : ∀ ts, Sequence.Realizes poly after ts →
      Sequence.Realizes poly before (ts ++ args)) :
    ResumePrefix C inputs ops poly after args :=
  ⟨h.wellFormed, fun ts ht => h.typed _ (hpop ts ht)⟩

theorem ResumePrefix.finish {C inputs ops poly vals args}
    (h : ResumePrefix C inputs ops poly vals args) (hC : wf_context C)
    (op : instr) (results : List types.ValueType) (hwf : wf_instr op)
    (hop : Instr_ok C op
      (.mk_functype (.mk_list args) (.mk_list (results.map Translate.valueType)))) :
    TypedPrefix C inputs (ops ++ [op]) poly (vals ++ results.map code.StackType.Val) := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Frames.realizes_append_concrete poly vals results ts).mp ht
    exact .seq C ops [op] inputs (pre ++ results.map Translate.valueType) (pre ++ args)
      (h.typed pre hp)
      (.frame C [op] pre args (results.map Translate.valueType)
        (.instr C op args _ hop hC hwf) hC (by simpa [Forall] using hwf))
      hC h.wellFormed (by simpa [Forall] using hwf)

end Itasca.MultiValue
