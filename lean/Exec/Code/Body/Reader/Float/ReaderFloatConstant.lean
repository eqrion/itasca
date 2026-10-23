import Exec.Code.Body.Reader.Common.ReaderWasm2
namespace Exec.Code
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
      ReaderPostWasm2 p out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.F32]) := by
  rw [dispatch_f32_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_f32_const.spec st.core data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f32 value)) out.pos :=
    .of_f32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm2 p out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.F32]) (ScalarConst.f32_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f32Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

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
      ReaderPostWasm2 p out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val types.ValueType.F64]) := by
  rw [dispatch_f64_const] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  have effect := code.read_f64_const.spec st.core data capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, decoded, values⟩ := effect
  dsimp only at controls decoded values
  refine ⟨value, callback, read, values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f64 value)) out.pos :=
    .of_f64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  apply reader_append_wasm2 p out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [code.StackType.Val types.ValueType.F64]) (ScalarConst.f64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f64Const wf value)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

end Exec.Code
