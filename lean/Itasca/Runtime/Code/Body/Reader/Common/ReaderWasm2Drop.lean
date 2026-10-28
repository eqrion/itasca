import Itasca.Runtime.Code.Body.Reader.Common.ReaderWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_drop_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP before =
      .ok (.Ok (), out, after)) :
    ∃ value values, visitor.on_drop before out value = .ok (.Ok (), after) ∧
      code.read_drop st.core = .ok (.Ok value, out) ∧
      StackSemantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPostWasm2 p out .DROP p.current.ctrl.polymorphic_base values := by
  rw [dispatch_drop] at accepted
  obtain ⟨value, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := code.pop_stack_type.segment st.core outer p.current.vals vals physicalBase
  change code.pop_stack_type st.core = .ok (.Ok value, out) at read
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, popped⟩ := effect
  dsimp only at controls position stack popped
  change StackSemantics.Popped (Control.polymorphic st.core) p.current.vals value values at popped
  rw [polymorphic] at popped
  refine ⟨value, values, callback, read, popped, ?_⟩
  have encoded : Wasm1.At data p.start (.plain .DROP) out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) (by simpa [position] using p.pos) .drop
  apply reader_append_wasm2 p out .DROP p.current.ctrl.polymorphic_base values .instr_case_2 (.plain encoded)
    (fun C wf priorTyped => popped.wasm2_prefix_drop C wf p.current.ops priorTyped)
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · exact encoded.declared _

end Itasca.Runtime.Code
