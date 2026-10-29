import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.Scalar.ReadersTotal
import Itasca.Runtime.Compiler.Body.Reader.Replay.BodySafety
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Relations.Calls.CallSafety

/-!
Direct-call reader bounds and callback safety, composing accepted reader steps with compiler resource obligations.
-/

/-! ## Reader Call Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
attribute [local step] code.pop_with_type.total code.pop_types.total
  Wasm2.ScalarReaders.reserved_zero

theorem reader_call_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_info st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.call_info
  step*

theorem reader_call_indirect_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_indirect_info st data env .Wasm2 ⦃ out => ∀ index table, out.1 = .Ok (index,table) →
      index.val < env.types.val.length ⦄ := by
  unfold code.call_indirect_info
  step*

end Itasca.Runtime.Compiler

end

/-! ## Reader Call Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

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
end Itasca.Runtime.Compiler

end
