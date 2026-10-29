import Itasca.Wasm2.Scalar.BasicReader
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack

/-!
The source effect of an accepted unreachable reader step.

Main declarations: `reader_unreachable_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.TerminalInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE before =
      .ok (.Ok (), out, after)) :
    visitor.on_unreachable before out = .ok (.Ok (), after) ∧
      out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      Wasm2.ReaderPost p out .UNREACHABLE true [] := by
  rw [dispatch_unreachable] at accepted
  obtain ⟨unit, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  cases unit
  have effect := p.read_unreachable byte
  rw [read, WP.spec_ok] at effect
  exact ⟨callback, effect.2⟩

end Itasca.Runtime.Compiler
