import Exec.Code.Body.Reader.Calls.ReaderCallBounds
import Exec.Code.Body.Reader.Common.ReaderBodySafety
import Exec.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Exec.Code.Local.Relations.Calls.CallSafety
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_call_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_call.dispatch]
  have reader := reader_call_bound st data env shape capacity
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state index read
    rw [read,WP.spec_ok] at reader
    have bound := reader index rfl
    exact compiler_on_call_total ops law compiler state index
      (by simpa [ready.namespaces.functions] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_call_indirect_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL_INDIRECT compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_call_indirect.dispatch]
  have reader := reader_call_indirect_bound st data env shape capacity
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state index read
    rw [read,WP.spec_ok] at reader
    have bound := reader index rfl
    exact compiler_on_call_indirect_total ops law compiler state index 0#u32
      (by simpa [ready.namespaces.signatures] using bound)
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_call_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 16#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_call]
  have reader := reader_call_info_bound st data env shape
  refine reader_body_run_reached _ _ _ _ (fun state after => ObservedStack after state.core.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state index read
    rw [read,WP.spec_ok] at reader
    have bound := reader index rfl
    exact compiler_on_call_total ops law compiler state.core index 
      (by simpa [ready.namespaces.functions] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_call_indirect_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 17#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_call_indirect]
  have reader := reader_call_indirect_info_bound st data env shape
  refine reader_body_run_reached _ _ _ _ (fun state after => ObservedStack after state.core.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state pair read
    obtain ⟨index,table⟩ := pair
    rw [read,WP.spec_ok] at reader
    have bound := reader index table rfl
    exact compiler_on_call_indirect_total ops law compiler state.core index table 
      (by simpa [ready.namespaces.signatures] using bound)
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
end Exec.Code
