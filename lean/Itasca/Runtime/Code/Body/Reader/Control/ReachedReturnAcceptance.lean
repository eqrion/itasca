import Itasca.Runtime.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Itasca.Runtime.Code.Local.Capacity.ReaderAcceptance
import Itasca.Runtime.Code.Local.Capacity.ReturnAvailability
import Itasca.Runtime.Code.Body.Reader.Control.ReaderReturnStack
import Itasca.Runtime.Code.Body.Reader.Common.ReaderRootFrame
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source return typing and the retained root frame discharge the actual
return callback's width check, including multi-value and vector results. -/
theorem reached_profile_return_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions (p.ft.results.val.map Translate.valueType) locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out.core bound)
    (reference : code.step_profile source st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨frame,found,resultWidth⟩ := reader_root_frame_wasm2 p compiler invariant.frames same
  rw [Wasm2.CallbackTrace.dispatch_return] at reference ⊢
  refine Wasm2.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value read _
  cases value
  have height : compiler.reachable = true → frame.results.val ≤ compiler.height.val := by
    intro live
    obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
    obtain ⟨front,input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve,p.signature]) values (by simpa [Control.base,controls] using base)
      (invariant.known live) (by simpa [Control.polymorphic,controls] using monomorphic live) read
    have layout := (invariant.live live).2.layout
    rw [input] at layout
    rw [resultWidth,layout.height,slots_append]
    omega
  exact compiler_return_available ops bound available compiler out.core demand frame (fun _ => found) height

end Itasca.Runtime.Code
