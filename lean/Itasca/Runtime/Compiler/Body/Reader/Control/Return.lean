import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Wasm2.Control.Return

/-!
The source effect of an accepted return reader step.

Main declarations: `reader_return_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ControlEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_return_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
    visitor.on_return before out.core = .ok (.Ok (), after) ∧
      Wasm2.returnStep st env index = .ok (.Ok (), out) ∧
      out.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      Wasm2.ReaderPost p out.core .RETURN true [] := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  cases value
  have effect := p.return_reader byte
  rw [read, WP.spec_ok] at effect
  exact ⟨callback, read, effect rfl⟩

end Itasca.Runtime.Compiler
