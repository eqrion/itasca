import Itasca.Wasm2.Scalar.NumericReader
import Itasca.Wasm2.Scalar.BasicReader
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Visitor.EventDispatch
import Itasca.Visitor.Erasure
import Itasca.Wasm2.Scalar.Step

/-!
Accepted scalar steps expose their actual callback together with the shared
`Wasm2.ReaderPost` certificate. Constants reuse the validator's reader facts;
nop and numeric adapters connect dispatch to the same source-prefix interface.
Compiler control, stack, and emission proofs consume these exact facts.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_nop_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_NOP before =
      .ok (.Ok (), out, after)) :
    visitor.on_nop before out = .ok (.Ok (), after) ∧
      Wasm2.ReaderPost p out .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  rw [dispatch_nop] at accepted
  obtain ⟨unit, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at read
  have state := read.2
  subst out
  exact ⟨callback, p.nop_reader byte⟩

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
      Wasm2.ReaderPost p out (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.I32]) := by
  rw [dispatch_i32_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_i32_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

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
      Wasm2.ReaderPost p out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.I64]) := by
  rw [dispatch_i64_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_i64_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

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
        Wasm2.ReaderPost p out operation.instruction p.current.ctrl.polymorphic_base values := by
  rw [dispatch_numeric visitor st.core data env ⟨locals, p.ft.results⟩ before opcode operation hook meaning handler] at accepted
  obtain ⟨unit, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  cases unit
  have encoded : Wasm1.At data p.start (.plain operation.instruction) st.core.pos :=
    .no_immediate p.inbounds byte p.pos (.numeric opcode operation meaning)
  have effect := p.numeric_reader operation st.core.pos capacity (.plain encoded) (encoded.declared _)
  dsimp only at effect
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, rest⟩ := effect
  obtain ⟨values, numeric, post⟩ := rest () rfl
  exact ⟨callback, read, controls, position, values, numeric, post⟩

end Itasca.Runtime.Compiler
