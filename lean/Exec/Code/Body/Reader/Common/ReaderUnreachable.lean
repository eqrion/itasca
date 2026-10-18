import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Local.Relations.Control.KnownControlStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE before =
      .ok (.Ok (), out, after)) :
    visitor.on_unreachable before out = .ok (.Ok (), after) ∧
      out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPostWasm2 p out .UNREACHABLE true [] := by
  rw [dispatch_unreachable] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  obtain ⟨marked, markedEq, markedVals, _, markedControls, markedPos⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st.core (p.parents.map Wasm2.Frames.Saved.ctrl) p.current.ctrl controls
      (by simp [base, vals]))
  have same : marked = out := by simpa [code.read_unreachable, markedEq] using read
  subst out
  refine ⟨callback, markedVals, ?_⟩
  apply reader_append_wasm2 p marked .UNREACHABLE true [] .instr_case_1
    (.plain (.no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [markedPos] using p.pos) .unreachable))
    (fun C wf priorTyped => priorTyped.unreachable wf) markedControls
  · simpa using markedVals
  · simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_unreachable_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step visitor st data env ctx code.OP_UNREACHABLE before =
      .ok (.Ok (), out, after)) :
    visitor.on_unreachable before out = .ok (.Ok (), after) ∧
      out.vals.val = st.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPostWasm1 p out .UNREACHABLE true [] := by
  rw [dispatch_unreachable] at accepted
  obtain ⟨unit, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  obtain ⟨marked, markedEq, markedVals, _, markedControls, markedPos⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st (p.parents.map Wasm1.Frames.Saved.ctrl) p.current.ctrl controls
      (by simp [base, vals]))
  have same : marked = out := by simpa [code.read_unreachable, markedEq] using read
  subst out
  refine ⟨callback, markedVals, ?_⟩
  apply reader_append_wasm1 p marked .UNREACHABLE true [] .instr_case_1
    ((.no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [markedPos] using p.pos) .unreachable))
    (fun C wf priorTyped => priorTyped.unreachable wf) markedControls
  · simpa using markedVals
  · simp

end Exec.Code
