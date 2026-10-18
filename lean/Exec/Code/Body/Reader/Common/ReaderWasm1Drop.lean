import Exec.Code.Body.Reader.Common.ReaderWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

theorem reader_drop_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step visitor st data env ctx code.OP_DROP before =
      .ok (.Ok (), out, after)) :
    ∃ value values, visitor.on_drop before out value = .ok (.Ok (), after) ∧
      code.read_drop st = .ok (.Ok value, out) ∧
      StackSemantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPostWasm1 p out .DROP p.current.ctrl.polymorphic_base values := by
  rw [dispatch_drop] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have physicalBase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := code.pop_stack_type.segment st outer p.current.vals vals physicalBase
  change code.pop_stack_type st = .ok (.Ok value, out) at read
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, popped⟩ := effect
  dsimp only at controls position stack popped
  change StackSemantics.Popped (Control.polymorphic st) p.current.vals value values at popped
  rw [polymorphic] at popped
  refine ⟨value, values, callback, read, popped, ?_⟩
  have encoded : Wasm1.At data p.start (.plain .DROP) out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) (by simpa [position] using p.pos) .drop
  apply reader_append_wasm1 p out .DROP p.current.ctrl.polymorphic_base values .instr_case_2 encoded
    (fun C wf priorTyped => popped.prefix_drop C wf p.current.ops priorTyped)
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · have length : ∀ {poly a b value}, StackSemantics.Popped poly a value b → b.length ≤ a.length + 1 := by
      intro poly a b value relation
      cases relation <;> simp <;> omega
    exact length popped

end Exec.Code
