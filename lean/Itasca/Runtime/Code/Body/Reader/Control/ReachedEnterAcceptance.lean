import Itasca.Runtime.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Itasca.Runtime.Code.Body.Reader.Common.ReaderEnterSafety
import Itasca.Runtime.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Code.Local.Capacity.ScopeAvailability
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Independent source validation supplies the captured block signature,
control base, and live condition layout for all three Wasm 2 scope openers.
Dead scope entry requires only the source signature and resource bounds. -/
theorem reached_profile_enter_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Pending data env .Wasm2 sourceLocals index st) (form : Frames.Form) (initialForm : form.Initial)
    {A V : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (demand : CallbackDemand compiler out.core bound) (scope : ScopeDemand compiler out.core bound)
    (pcRoom : compiler.function.code.length+1 ≤ U32.max)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (reference : code.step_profile source st data env ctx index .Wasm2 form.opcode before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 form.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  obtain ⟨bt,ins,outs,remaining,base,_,read,post⟩ := reader_enter_wasm2 p form initialForm source before after out ctx
    byte reference
  obtain ⟨signature,selected,_⟩ := signatures.select post.inputs post.outputs
  have controls := (post.front initialForm).1
  have valuesFit : (Frames.Saved.fresh base form bt ins outs).ctrl.value_stack_base.val ≤ out.core.vals.val.length := by
    exact (post.front initialForm).2.1
  have conditionLayout : compiler.reachable = true → form.kind = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32]) := by
    intro live thenKind
    rcases initialForm with rfl | rfl | rfl
    · cases thenKind
    · cases thenKind
    · obtain ⟨front,_,oldTypes,_⟩ := post.callback_inputs (.inr (.inr rfl)) (monomorphic live)
        (invariant.known live) (invariant.live live).2.layout signatures
      refine ⟨front ++ ins.map Translate.valueType,?_⟩
      have layout := (invariant.live live).2.layout
      simpa [Frames.Form.args,List.append_assoc] using oldTypes ▸ layout
  have callback := compiler_enter_available ops bound available compiler out.core demand scope
    (Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Frames.Saved.ctrl) form.kind bt signature
    controls selected valuesFit pcRoom conditionLayout
  have actual : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (enterAction form bt)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
    rcases initialForm with rfl | rfl | rfl <;> exact callback
  have dispatch : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 form.opcode compiler =
      CallbackTrace.bodyRun (code.enter_info st data env .Wasm2 form.kind)
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler := by
    rcases initialForm with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block _ _ _ _ _ _ _ _
    · exact CallbackTrace.dispatch_loop _ _ _ _ _ _ _ _
    · exact CallbackTrace.dispatch_if _ _ _ _ _ _ _ _
  rw [dispatch]
  exact CallbackTrace.bodyRun.available_of_read _ _ _ compiler bt out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)) read actual

end Itasca.Runtime.Code
