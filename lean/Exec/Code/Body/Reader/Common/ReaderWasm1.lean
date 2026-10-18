import Exec.Code.Body.Reader.Common.ReaderBasic
import Itasca.Wasm1.StepScalar
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

structure ReaderPostWasm1 {data env ctx bt st}
    (pending : Pending data env ctx bt st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType) : Prop where
  encoded : At data pending.start (.plain instruction) out.pos
  opened : Frames.Open (EnvTranslation.context env ctx) out pending.parents
    (pending.current.advance (.plain instruction) instruction poly values)
  after : pending.After out

theorem reader_append_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : ∀ C, wf_context C →
      Sequence.TypedPrefix C p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      Sequence.TypedPrefix C (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (stack : out.vals.val = st.vals.val.take p.current.ctrl.value_stack_base.val ++ values)
    (length : values.length ≤ p.current.vals.length + 1)
    (profile : ∀ C, Wasm1.Instruction C instruction := by intro C; exact .leaf _ _ (by trivial)) :
    ReaderPostWasm1 p out instruction poly values := by
  obtain ⟨C, outer, spine, header, base, priorTyped, ctrls, vals⟩ := p.opened
  have Cwf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ctx))
    p.current.form p.current.ctrl.block_type
  have newTyped := typed _ Cwf priorTyped
  have newVals : out.vals.val = outer ++ values := by simpa [vals, base] using stack
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.prior, .simple header.emits (.plain instruction wf),
      header.profile.append (.cons (profile _) (.nil _)), header.priorProfile⟩, base, newTyped, controls, newVals⟩
  · exact p.append_result C outer spine header base ctrls vals out instruction poly values
      wf encoded newTyped controls newVals length (profile _)

theorem reader_nop_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step visitor st data env ctx code.OP_NOP before =
      .ok (.Ok (), out, after)) :
    visitor.on_nop before out = .ok (.Ok (), after) ∧
      ReaderPostWasm1 p out .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  rw [dispatch_nop] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at read
  have state := read.2
  subst out
  refine ⟨callback, ?_⟩
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  apply reader_append_wasm1 p st .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.no_immediate p.inbounds (by simpa [global_simps] using byte) p.pos .nop)
    (fun C wf priorTyped => priorTyped.nop wf)
  · simpa using controls
  · simp [vals, base]
  · omega

theorem reader_i32_const_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step visitor st data env ctx code.OP_I32_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_i32_const before out value = .ok (.Ok (), after) ∧
      code.read_i32_const st data = .ok (.Ok value, out) ∧
      out.vals.val = st.vals.val ++ [.Val .I32] ∧
      ReaderPostWasm1 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.I32]) := by
  rw [dispatch_i32_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_i32_const.spec st data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (Spec.i32Const value)) out.pos :=
    .of_s32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm1 p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.I32]) (Spec.i32Const_wf value) encoded
    (fun C wf priorTyped => priorTyped.i32Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · simp

theorem reader_i64_const_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step visitor st data env ctx code.OP_I64_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_i64_const before out value = .ok (.Ok (), after) ∧
      code.read_i64_const st data = .ok (.Ok value, out) ∧
      out.vals.val = st.vals.val ++ [.Val .I64] ∧
      ReaderPostWasm1 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.I64]) := by
  rw [dispatch_i64_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_i64_const.spec st data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.i64 value)) out.pos :=
    .of_s64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm1 p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.I64]) (ScalarConst.i64_wf value) encoded
    (fun C wf priorTyped => priorTyped.i64Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · simp

theorem reader_numeric_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (opcode : U8)
    (operation : Numeric.Operation) (hook : NumericHook)
    (capacity : st.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (handler : NumericHook.ofOpcode opcode = some hook)
    (accepted : code.step visitor st data env ctx opcode before =
      .ok (.Ok (), out, after)) :
    invoke visitor before (.op out (.numeric hook)) = .ok (.Ok (), after) ∧
      Numeric.read operation st = .ok (.Ok (), out) ∧
      out.ctrls = st.ctrls ∧ out.pos = st.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPostWasm1 p out operation.instruction p.current.ctrl.polymorphic_base values := by
  rw [dispatch_numeric visitor st data env ctx before opcode operation hook meaning handler] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases unit
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have physicalBase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := Numeric.read.segment operation st outer p.current.vals vals physicalBase capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, numeric⟩ := effect
  dsimp only at controls position stack length numeric
  rw [polymorphic] at numeric
  refine ⟨callback, read, controls, position, values, numeric, ?_⟩
  have encoded : Wasm1.At data p.start (.plain operation.instruction) out.pos :=
    .no_immediate p.inbounds byte (by simpa [position] using p.pos) (.numeric opcode operation meaning)
  apply reader_append_wasm1 (profile := Numeric.opcode_profile opcode operation meaning) p out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed encoded
    (fun C wf priorTyped => numeric.prefix C wf p.current.ops operation.instruction priorTyped
      operation.wellFormed (operation.typed C wf))
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · exact length

end Exec.Code
