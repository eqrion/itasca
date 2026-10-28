import Itasca.Runtime.Code.Body.Reader.Common.ReaderSafety
import Itasca.Runtime.Code.Body.Reader.Local.ReaderLocalBounds
import Itasca.Runtime.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Code.Local.Relations.Local.LocalSafety
import Itasca.Wasm2.Scalar.ReadersTotal
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual local.get dispatch returns normally on parsing rejection as well as
compiler rejection; accepted reads supply their checked local index. -/
theorem compiler_reader_local_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
end Itasca.Runtime.Code
