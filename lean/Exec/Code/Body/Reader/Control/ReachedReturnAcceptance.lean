import Exec.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.ReturnAvailability
import Exec.Code.Body.Reader.Control.ReaderReturnStack
import Exec.Code.Body.Reader.Common.ReaderRootFrame
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source return typing and the retained root frame discharge the actual
return callback's width check, including multi-value and vector results. -/
theorem reached_profile_return_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
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

/-- Wasm 1 uses its source result descriptor and the same actual return
callback, without assuming a successful compiler execution. -/
theorem reached_reader_return_available_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions (ctx.results.val.map Translate.valueType) locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (bodyResults : Control.resultTypes bt = ctx.results.val.map Translate.valueType)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out bound)
    (reference : code.step source st data env ctx code.OP_RETURN before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_RETURN compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨frame,found,resultWidth⟩ := reader_root_frame_wasm1 p compiler invariant.frames same
  rw [bodyResults] at resultWidth
  rw [OpDispatch.dispatch_return] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_return st ctx)
    (fun v state (_ : Unit) => source.on_return v state)
    (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_return v state)
    before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value read _
  have height : compiler.reachable = true → frame.results.val ≤ compiler.height.val := by
    intro live
    cases value
    obtain ⟨_,outer,_,_,base,_,controls,values⟩ := p.opened
    obtain ⟨front,input⟩ := reader_return_stack_wasm1 st out ctx outer p.current.vals values
      (by simpa [Control.base,controls] using base) (invariant.known live)
      (by simpa [Control.polymorphic,controls] using monomorphic live) read
    have layout := (invariant.live live).2.layout
    rw [input] at layout
    rw [resultWidth,layout.height,slots_append]
    omega
  exact compiler_return_available ops bound available compiler out demand frame (fun _ => found) height

end Exec.Code
