import Itasca.Runtime.Compiler.Body.Reader.Replay.Run
import Itasca.Wasm2.Scalar.Step

/-!
A reader advances this precise source zipper; source instructions are not recovered from an unrelated existential post-state witness.

Main declarations: `ReaderPostWasm2`. A direct consumer is `Compiler.Body.Reader.Control.Boundary`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- A reader advances this precise source zipper; source instructions are not
recovered from an unrelated existential post-state witness. -/
structure ReaderPostWasm2 {data env locals index st}
    (pending : Pending data env .Wasm2 locals index st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType) : Prop where
  encoded : At data pending.start (.plain instruction) out.pos
  opened : Frames.Open env (bodyContext env locals pending.ft) {st with core := out}
    pending.parents (pending.current.advance (.plain instruction) instruction poly values)
  after : pending.After {st with core := out}

theorem reader_append_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.OpIterState)
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
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderPostWasm2 p out instruction poly values := by
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
      wf encoded newTyped controls newBlocks newVals (fun h => nomatch h) declared

theorem reader_nop_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_NOP before =
      .ok (.Ok (), out, after)) :
    visitor.on_nop before out = .ok (.Ok (), after) ∧
      ReaderPostWasm2 p out .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  rw [dispatch_nop] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at read
  have state := read.2
  subst out
  refine ⟨callback, ?_⟩
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  apply reader_append_wasm2 p st.core .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.plain (.no_immediate p.inbounds (by simpa [global_simps] using byte) p.pos .nop))
    (fun C wf priorTyped => priorTyped.nop wf)
  · simpa using controls
  · simp [vals, base]
  · simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_i32_const_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I32_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_i32_const before out value = .ok (.Ok (), after) ∧
      code.read_i32_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .I32] ∧
      ReaderPostWasm2 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.I32]) := by
  rw [dispatch_i32_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_i32_const.spec st.core data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (Spec.i32Const value)) out.pos :=
    .of_s32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm2 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.I32]) (Spec.i32Const_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i32Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

theorem reader_i64_const_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I64_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_i64_const before out value = .ok (.Ok (), after) ∧
      code.read_i64_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .I64] ∧
      ReaderPostWasm2 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.I64]) := by
  rw [dispatch_i64_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_i64_const.spec st.core data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.i64 value)) out.pos :=
    .of_s64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm2 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.I64]) (ScalarConst.i64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i64Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

theorem reader_numeric_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (opcode : U8)
    (operation : Numeric.Operation) (hook : NumericHook)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (handler : NumericHook.ofOpcode opcode = some hook)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode before =
      .ok (.Ok (), out, after)) :
    invoke visitor before (.op out (.numeric hook)) = .ok (.Ok (), after) ∧
      Numeric.read operation st.core = .ok (.Ok (), out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPostWasm2 p out operation.instruction p.current.ctrl.polymorphic_base values := by
  rw [dispatch_numeric visitor st.core data env ⟨locals, p.ft.results⟩ before opcode operation hook meaning handler] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases unit
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := Numeric.read.segment operation st.core outer p.current.vals vals physicalBase capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, numeric⟩ := effect
  dsimp only at controls position stack length numeric
  rw [polymorphic] at numeric
  refine ⟨callback, read, controls, position, values, numeric, ?_⟩
  have encoded : Wasm1.At data p.start (.plain operation.instruction) out.pos :=
    .no_immediate p.inbounds byte (by simpa [position] using p.pos) (.numeric opcode operation meaning)
  apply reader_append_wasm2 p out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed (.plain encoded)
    (fun C wf priorTyped => numeric.wasm2_prefix C wf p.current.ops operation.instruction priorTyped
      operation.wellFormed (operation.typed C wf))
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · exact encoded.declared _

end Itasca.Runtime.Code
