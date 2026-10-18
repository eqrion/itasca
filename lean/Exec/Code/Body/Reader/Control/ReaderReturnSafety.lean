import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Reader.Common.ReaderBodySafety
import Itasca.Wasm2.Trace.ControlRecords
import Exec.Code.Local.Relations.Common.TerminalSafety
import Exec.Code.Body.Relations.Control.ReachedControlSafety
import Itasca.Wasm2.Control.Total
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem return_reader_total (state : code.OpIterState) (ctx : code.Context)
    (shape : Control.Shape state) : code.read_return state ctx ⦃ _ => True ⦄ := by
  unfold code.read_return
  step with code.pop_types.total state ctx.results.deref shape
    as ⟨status,middle,shaped,_,_,_,_⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unitValue =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with code.mark_unreachable_total middle shaped

theorem compiler_return_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (ctx : code.Context) (shape : Control.Shape state)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CoreVisitor.run (code.read_return state ctx)
      (fun c s _ => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_return c s)
      compiler ⦃ out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply reader_run_reached _ _ compiler (fun s c => ObservedStack c s.vals.val)
  · exact return_reader_total state ctx shape
  · intro out value read
    exact compiler_on_return_total ops law compiler out bodyFrame codeFits sourceFits coordinate

theorem StructuredCompilerPrefixWithTables.return_reader_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (ctx : code.Context) (shape : Control.Shape state)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CoreVisitor.run (code.read_return state ctx)
      (fun c s _ => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_return c s)
      compiler ⦃ out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  have capacities := invariant.capacities bounded
  apply compiler_return_reader_total ops law compiler state ctx shape _ capacities.1 capacities.2.1 coordinate
  intro live
  obtain ⟨prior,frame,frames,_⟩ := invariant.frames.split
  simp [frames]

theorem compiler_return_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : module.Env) (index : U32) (shape : Control.Shape state.core)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    Wasm2.CallbackTrace.bodyRun (Wasm2.returnStep state env index)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun _ => .return_) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (Wasm2.CallbackTrace.return_position state env index shape) (by simp)
  · intro out value read
    exact compiler_on_return_total ops law compiler out.core bodyFrame codeFits sourceFits coordinate
end Exec.Code
