import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Visitor.EventDispatch
import Itasca.Visitor.Erasure
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalSafety
import Itasca.Wasm2.Scalar.ReadersTotal

/-!
Local-index bounds and normal return of local get/set/tee reader callbacks.
-/

/-! ## Reader Local Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful local parsing checks the namespace before the compiler callback,
including unreachable stacks and without assuming successful compilation. -/
theorem reader_local_get_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_get st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨next,pushed,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact post.2.choose

theorem reader_local_set_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_set st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose

theorem reader_local_tee_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_tee st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at tail
      obtain ⟨final,pushed,tail⟩ := ResultFacts.bind_ok_inv _ _ _ tail
      simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose
end Itasca.Runtime.Compiler

end

/-! ## Reader Local Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual local.get dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_get.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.local_get st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_get_bound st state data ctx index read
    exact compiler_local_get_total ops law compiler state index
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

/-- Actual local.set dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_set.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.local_set st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_set_bound st state data ctx index read
    exact compiler_local_write_total ops law compiler state index false
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

/-- Actual local.tee dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_tee_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_local_tee.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Wasm2.ScalarReaders.local_tee st data ctx shape capacity) (by simp)
  · intro state index read
    have bound := reader_local_tee_bound st state data ctx index read
    exact compiler_local_write_total ops law compiler state index true
      (by simpa [ready.namespaces.offsets] using bound)
      (by simpa [ready.namespaces.locals] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Runtime.Compiler

end
