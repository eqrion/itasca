import Itasca.Runtime.Code.Body.Reader.Common.ReaderSafety
import Itasca.Runtime.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- Body-state readers invoke the compiler only after their actual successful
parse and validation result. Rejections on either side return normally. -/
theorem reader_body_run_reached {T V : Type}
    (read : Result (core.result.Result T error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : T → Action)
    (before : V) (post : code.BodyState → V → Prop)
    (reader : read ⦃ _ => True ⦄)
    (callback : ∀ state value, read = .ok (.Ok value,state) →
      invoke visitor before (.op state.core (action value)) ⦃ out => out.1 = .Ok () → post state out.2 ⦄) :
    CallbackTrace.bodyRun read visitor action before ⦃ out =>
      out.1 = .Ok () → post out.2.1 out.2.2 ⦄ := by
  obtain ⟨⟨result,state⟩,readEq,_⟩ := WP.spec_imp_exists reader
  cases result with
  | Err error => simp [CallbackTrace.bodyRun,readEq]
  | Ok value =>
    obtain ⟨⟨result,after⟩,called,ready⟩ := WP.spec_imp_exists (callback state value readEq)
    cases result with
    | Err error => simp [CallbackTrace.bodyRun,readEq,called,hookResult]
    | Ok unitValue =>
      cases unitValue
      simpa [CallbackTrace.bodyRun,readEq,called,hookResult,WP.spec_ok] using ready rfl
end Itasca.Runtime.Code
