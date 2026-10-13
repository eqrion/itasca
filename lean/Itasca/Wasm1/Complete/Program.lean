import Itasca.Wasm1.Complete.Frame

open Aeneas Aeneas.Std

namespace Itasca.Completeness

/-- Execution of a typed instruction list within one concrete control frame. -/
def Program (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (tokens : List Wasm1.Token) (ops : List instr) : Prop :=
  ∀ (C : context) (st : code.OpIterState) (f : Frame st) (next : Usize)
    (input output : List valtype),
    EnvTranslation.Matches env ctx C → C.LABELS = Control.labels st.ctrls.val →
    Wasm1.Bounds data st → Wasm1.Consumed data st.pos tokens next →
    Sequence.Realizes f.current.polymorphic_base f.operands input →
    Instrs_ok C ops (.mk_functype (.mk_list input) (.mk_list output)) →
    Wasm1.Instructions C ops →
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧ f.Output output s ∧
      Wasm1.Bounds data s

/-- The normalized head instruction has a primitive generated typing rule
and a preserved prefix on its operand stack. -/
def AtomProgram (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (tokens : List Wasm1.Token) (op : instr) : Prop :=
  ∀ (C : context) (st : code.OpIterState) (f : Frame st) (next : Usize)
    (front input output : List valtype),
    EnvTranslation.Matches env ctx C → C.LABELS = Control.labels st.ctrls.val →
    Wasm1.Bounds data st → Wasm1.Consumed data st.pos tokens next →
    Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    Wasm1.Instruction C op →
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧
      f.Output (front ++ output) s ∧ Wasm1.Bounds data s

def SmallerPrograms (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (n : Nat) : Prop :=
  ∀ tokens ops, tokens.length < n → Wasm1.Emits tokens ops → Program data env ctx tokens ops

theorem Frame.Output.transfer {st s t} {f : Frame st} {g : Frame s}
    {out : List valtype} (h : g.Output out t)
    (hp : g.parents = f.parents) (ho : g.outer = f.outer)
    (hk : g.current.kind = f.current.kind)
    (hb : g.current.block_type = f.current.block_type)
    (hsig : g.current.signature = f.current.signature)
    (hbase : g.current.value_stack_base = f.current.value_stack_base) : f.Output out t := by
  obtain ⟨poly, operands, hc, hv, ht⟩ := h
  have he : {g.current with polymorphic_base := poly} =
      {f.current with polymorphic_base := poly} := by
    cases hg : g.current
    cases hf : f.current
    simp only [hg, hf] at hk hb hsig hbase
    simp_all
  exact ⟨poly, operands, by simpa [hp, he] using hc, by simpa [ho] using hv, ht⟩

/-- Left-to-right execution follows a declarative derivation even when that
derivation uses arbitrary sequence, framing, and subsumption rules. The atom
obligation recursively receives only strictly smaller nested bodies. -/
theorem program_of_atoms (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (hatom : ∀ tokens op, Wasm1.Atom tokens op →
      SmallerPrograms data env ctx tokens.length → AtomProgram data env ctx tokens op)
    (tokens : List Wasm1.Token) (ops : List instr) (hemits : Wasm1.Emits tokens ops) :
    Program data env ctx tokens ops := by
  generalize hn : tokens.length = n
  induction n using Nat.strong_induction_on generalizing tokens ops with
  | h n ih =>
    intro C st f next input output hmatch hlabels hbounds hbytes hreal htyped hprofile
    cases ops with
    | nil =>
      have hnil := Wasm1.Emits.empty_iff.mp hemits
      subst tokens
      have he := Wasm1.Consumed.empty_eq hbytes rfl
      subst next
      exact ⟨st, .nil st, rfl,
        f.output_self (DeclarativeComplete.empty_realizes hreal htyped), hbounds⟩
    | cons op ops =>
      obtain ⟨first, rest, he, hfirst, hrest⟩ := Wasm1.Emits.cons_iff.mp hemits
      subst tokens
      have hfirst_len : first.length ≤ n := by simp only [List.length_append] at hn; omega
      have hrest_len : rest.length < n := by
        have hnonempty := hfirst.nonempty
        have hpos : 0 < first.length := List.length_pos_iff.mpr hnonempty
        simp only [List.length_append] at hn
        omega
      obtain ⟨middle, hfirstbytes, hrestbytes⟩ := Wasm1.Consumed.split hbytes
      obtain ⟨front, ins, outs, hop, hinput, htail⟩ :=
        DeclarativeComplete.head_realizes hreal htyped
      cases hprofile with
      | cons hfirstprofile hrestprofile =>
        have hsmaller : SmallerPrograms data env ctx first.length := by
          intro ts es hlen he
          exact ih ts.length (by omega) ts es he rfl
        obtain ⟨mid, hrun, hpos, hout, hbound⟩ :=
          hatom first op hfirst hsmaller C st f middle front ins outs hmatch hlabels
            hbounds hfirstbytes hinput hop hfirstprofile
        obtain ⟨g, hgp, hgo, hgk, hgb, hgsig, hgba, hgr⟩ := hout.next
        have hrestbytes' : Wasm1.Consumed data mid.pos rest next := by simpa [hpos] using hrestbytes
        have hlabels' : C.LABELS = Control.labels mid.ctrls.val := hlabels.trans hout.labels.symm
        obtain ⟨last, hrun', hpos', hout', hbound'⟩ :=
          ih rest.length hrest_len rest ops hrest rfl C mid g next _ _
            hmatch hlabels' hbound hrestbytes' hgr htail hrestprofile
        exact ⟨last, hrun.append hrun', hpos',
          hout'.transfer hgp hgo hgk hgb hgsig hgba, hbound'⟩

end Itasca.Completeness
