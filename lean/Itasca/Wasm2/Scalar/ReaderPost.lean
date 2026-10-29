import Itasca.Wasm2.Invariant

/-!
Exact source-prefix advancement shared by validator preservation and compiler replay.
`ReaderPost` retains the decoded instruction and the original frame zipper as well
as the ordinary `Pending.After` invariant, for either validation profile.
-/

namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

/-- A reader advances this precise source zipper; source instructions are not
recovered from an unrelated existential post-state witness. -/
structure ReaderPost {data env profile locals index st}
    (pending : Pending data env profile locals index st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType) : Prop where
  encoded : At data pending.start (.plain instruction) out.pos
  opened : Frames.Open env (bodyContext env locals pending.ft) {st with core := out}
    pending.parents (pending.current.advance (.plain instruction) instruction poly values)
  after : pending.After {st with core := out}

/-- Retain the exact decoded instruction under its original frame context. -/
theorem Pending.append_reader_context {data env profile locals index st}
    (p : Pending data env profile locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (out : code.OpIterState) (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (blocks : ({core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (stack : out.vals.val = outer ++ values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (wasm1 : profile = .Wasm1 → Wasm1.At data p.start (.plain instruction) out.pos ∧
      Wasm1.Instruction (Frames.enter C p.current.form p.current.ins p.current.outs) instruction := by intro h; cases h) :
    Wasm2.ReaderPost p out instruction poly values := by
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain instruction wf)⟩, base, typed, controls, blocks, stack⟩
  · exact p.append_result C outer spine header base {core := out} instruction poly values
      wf encoded typed controls blocks stack wasm1 declared

/-- Append an independently encoded instruction to the same source zipper.
Wasm 1.0 additionally requires its grammar and instruction restriction; that
obligation is vacuous for Wasm 2.0. -/
theorem Pending.append_reader {data env profile locals index st}
    (p : Pending data env profile locals index st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : ∀ C, wf_context C →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := poly}])
    (stack : out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ++ values)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (wasm1 : profile = .Wasm1 → ∀ C, Wasm1.At data p.start (.plain instruction) out.pos ∧
      Wasm1.Instruction C instruction := by intro h; cases h) :
    ReaderPost p out instruction poly values := by
  obtain ⟨C, outer, spine, header, base, priorTyped, ctrls, blocks, vals⟩ := p.opened
  have Cwf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have newTyped := typed _ Cwf priorTyped
  have newVals : out.vals.val = outer ++ values := by simpa [vals, base] using stack
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
    simpa [controls, ctrls] using blocks
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain instruction wf)⟩, base, newTyped, controls, newBlocks, newVals⟩
  · exact p.append_result C outer spine header base {st with core := out} instruction poly values
      wf encoded newTyped controls newBlocks newVals (fun h => wasm1 h _) declared

end Itasca.Wasm2
