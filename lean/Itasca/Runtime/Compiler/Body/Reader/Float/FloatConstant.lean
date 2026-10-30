import Itasca.Wasm2.Scalar.BasicReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
Reader inversion for 32-bit and 64-bit floating-point constants.

Main declarations: `reader_f32_const_wasm2` and `reader_f64_const_wasm2`. A direct consumer is `Compiler.Body.Reader.Float.ConstantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
open Itasca.Wasm1 in
open Itasca.Wasm2 in
theorem reader_f32_const_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f32_const before out value = .ok (.Ok (), after) ∧
      code.read_f32_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F32] ∧
      Wasm2.ReaderPost p out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F32]) := by
  rw [dispatch_f32_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f32_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

open Itasca.Wasm2 in
theorem reader_f64_const_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f64_const before out value = .ok (.Ok (), after) ∧
      code.read_f64_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F64] ∧
      Wasm2.ReaderPost p out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F64]) := by
  rw [dispatch_f64_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f64_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

end Itasca.Runtime.Compiler
