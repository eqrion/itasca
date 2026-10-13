import Itasca.Wasm1.Complete.Program

open Aeneas Aeneas.Std

namespace Itasca.Completeness

def LeafContract (data : Slice U8) (env : module.Env) (ctx : code.Context) : Prop :=
  ∀ (C : context) (st : code.OpIterState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype),
    EnvTranslation.Matches env ctx C → C.LABELS = Control.labels st.ctrls.val →
    st.vals.val.length < Usize.max →
    Wasm.Immediate opcode (.plain op) bytes → Wasm.BytesAt data st.pos bytes next →
    Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    Wasm1.Instruction C op → StepResult f data env ctx opcode next (front ++ output)

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
    have hlimit := Body.byte_limit_room
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

end Itasca.Completeness
