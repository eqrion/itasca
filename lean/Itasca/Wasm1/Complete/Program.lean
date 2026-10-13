import Itasca.Wasm1.Complete.Frame

/-!
# Executing typed instruction lists

`Program` says that the instructions of a token sequence run successfully in one control frame
under a typing derivation, and `AtomProgram` is the same statement for a single instruction.
`program_of_atoms` derives `Program` from `AtomProgram` by induction on the declarative
derivation, and `atom_of_leaf` builds `AtomProgram` for a leaf instruction from `LeafContract`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

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

/-- Execution of one instruction that has a primitive generated typing rule, with an untouched
prefix `front` below its inputs on the operand stack. -/
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

/-- `Program` holds for every emitted token sequence shorter than `n`. -/
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

/-- Left-to-right execution follows a declarative derivation, including its sequence, framing
and subsumption rules. The atom hypothesis receives `Program` only for strictly shorter nested
bodies. -/
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

end Itasca.Wasm1.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- The completeness statement for a non-structured instruction `op` with encoded immediates
`bytes`: `code.step` accepts it, given its primitive generated typing. -/
def LeafContract (data : Slice U8) (env : module.Env) (ctx : code.Context) : Prop :=
  ∀ (C : context) (st : code.OpIterState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype),
    EnvTranslation.Matches env ctx C → C.LABELS = Control.labels st.ctrls.val →
    st.vals.val.length < Usize.max →
    Wasm1.Immediate opcode (.plain op) bytes → Wasm1.BytesAt data st.pos bytes next →
    Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    Wasm1.Instruction C op → StepResult f data env ctx opcode next (front ++ output)

/-- A `LeafContract` yields `AtomProgram` for the single token of a plain instruction. -/
theorem atom_of_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (hstep : LeafContract data env ctx) (op : instr) :
    AtomProgram data env ctx [.plain op] op := by
  intro C st f next front input output hmatch hlabels hbounds hbytes hreal htyped hprofile
  have hat := hbytes.single
  obtain ⟨opcode, pos, bytes, hread, hpos, himmediate, hspan⟩ := hat.read_op st rfl
  let decoded := {st with pos := pos}
  let g : Frame decoded :=
    ⟨f.parents, f.current, f.outer, f.operands, f.ctrls, f.vals, f.base⟩
  have hcap : decoded.vals.val.length < Usize.max := by
    have hlimit := limits.MAX_FUNCTION_BYTES.room
    have hlen := hat.span
    have hs := hbounds.size
    have hv := hbounds.vals
    dsimp [decoded]
    omega
  obtain ⟨s, hrun, hcursor, hout, hlen⟩ :=
    hstep C decoded g opcode op bytes next front input output hmatch hlabels hcap
      himmediate hspan hreal htyped hprofile
  have hout' : f.Output (front ++ output) s := hout
  refine ⟨s, .single f.nonempty hread hrun, hcursor, hout', ?_⟩
  refine ⟨hbounds.size, ?_, ?_, ?_⟩
  · simpa [hcursor] using hat.span.2
  · have hv := hbounds.vals
    have hs := hat.span.1
    change s.vals.val.length ≤ st.vals.val.length + 1 at hlen
    rw [hcursor]
    omega
  · obtain ⟨poly, operands, hc, _, _⟩ := hout'
    have hcl : s.ctrls.val.length = st.ctrls.val.length := by simp [hc, f.ctrls]
    have hcb := hbounds.ctrls
    have hs := hat.span.1
    rw [hcl, hcursor]
    omega

end Itasca.Wasm1.Completeness
