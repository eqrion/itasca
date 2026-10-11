import Itasca.MultiValue.CompletenessFrame
import Itasca.MultiValue.Execution

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Completeness

/-- Execution of a typed instruction list within one concrete control frame. -/
def Program (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (tokens : List Token) (ops : List instr) : Prop :=
  ∀ (C : context) (st : multi_value.State) (f : Frame st) (next : Usize)
    (input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands input →
    Instrs_ok C ops (.mk_functype (.mk_list input) (.mk_list output)) →
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧ f.Output output s ∧
      Bounds data s

/-- The normalized head instruction has a primitive generated typing rule
and a preserved prefix on its operand stack. -/
def AtomProgram (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (tokens : List Token) (op : instr) : Prop :=
  ∀ (C : context) (st : multi_value.State) (f : Frame st) (next : Usize)
    (front input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧ Bounds data s

def SmallerPrograms (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (n : Nat) : Prop :=
  ∀ tokens ops, tokens.length < n → Emits tokens ops → Program data env ctx index tokens ops

/-- Left-to-right execution follows a declarative derivation even when that
derivation uses arbitrary sequence, framing, and subsumption rules. The atom
obligation recursively receives only strictly smaller nested bodies. -/
theorem program_of_atoms (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (hatom : ∀ tokens op, Atom tokens op →
      SmallerPrograms data env ctx index tokens.length → AtomProgram data env ctx index tokens op)
    (tokens : List Token) (ops : List instr) (hemits : Emits tokens ops) :
    Program data env ctx index tokens ops := by
  generalize hn : tokens.length = n
  induction n using Nat.strong_induction_on generalizing tokens ops with
  | h n ih =>
    intro C st f next input output hmatch hlabels hbounds hbytes hreal htyped
    cases ops with
    | nil =>
      have hnil := Emits.empty_iff.mp hemits
      subst tokens
      have he := Consumed.empty_eq hbytes rfl
      subst next
      exact ⟨st, .nil st, rfl,
        f.output_self (DeclarativeComplete.empty_realizes hreal htyped), hbounds⟩
    | cons op ops =>
      obtain ⟨first, rest, he, hfirst, hrest⟩ := Emits.cons_iff.mp hemits
      subst tokens
      have hfirst_len : first.length ≤ n := by simp only [List.length_append] at hn; omega
      have hrest_len : rest.length < n := by
        have hnonempty := hfirst.nonempty
        have hpos : 0 < first.length := List.length_pos_iff.mpr hnonempty
        simp only [List.length_append] at hn
        omega
      obtain ⟨middle, hfirstbytes, hrestbytes⟩ := Consumed.split hbytes
      obtain ⟨front, ins, outs, hop, hinput, htail⟩ :=
        DeclarativeComplete.head_realizes hreal htyped
      have hsmaller : SmallerPrograms data env ctx index first.length := by
        intro ts es hlen he
        exact ih ts.length (by omega) ts es he rfl
      obtain ⟨mid, hrun, hpos, hout, hbound⟩ :=
        hatom first op hfirst hsmaller C st f middle front ins outs hmatch hlabels
          hbounds hfirstbytes hinput hop
      obtain ⟨g, _, _, hgp, hgo, hgk, hgb, hgba, hgr⟩ := hout.next
      have hrestbytes' : Consumed data mid.core.pos rest next := by simpa [hpos] using hrestbytes
      have hlabels' : Labels env mid C := hout.labels hlabels
      obtain ⟨last, hrun', hpos', hout', hbound'⟩ :=
        ih rest.length hrest_len rest ops hrest rfl C mid g next _ _
          hmatch hlabels' hbound hrestbytes' hgr htail
      exact ⟨last, hrun.append hrun', hpos',
        hout'.transfer hout.2 hgp hgo hgk hgb hgba, hbound'⟩

end Itasca.MultiValue.Completeness
