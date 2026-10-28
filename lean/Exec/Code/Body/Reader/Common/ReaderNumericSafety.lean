import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Exec.Code.Local.Lowering.Common.NumericSafety
import Exec.Code.Local.Lowering.Float.FloatSafety
import Exec.Code.Body.Reader.Common.NumericReaderFacts
import Exec.Code.Body.Reader.Float.FloatReaderFacts

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every base integer numeric reader and its concrete compiler callback return
normally from a reached callback boundary, including parser and visitor errors. -/
theorem compiler_reader_numeric_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := integer_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Numeric.read.total operation st shape capacity) (by simp)
  · intro state value read
    obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := integer_reader_facts ops compiler state op base
    have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
    subst hook'
    rw [callback]
    exact compiler_numeric_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits

/-- Base floating-point numeric readers use the same raw stack bounds; neither
floating-point execution nor a FloatOps law is involved in compilation. -/
theorem compiler_reader_float_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := float_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Numeric.read.total operation st shape capacity) (by simp)
  · intro state value read
    obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := float_reader_facts ops compiler state op base
    have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
    subst hook'
    rw [callback]
    exact compiler_float_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits

end Itasca.Runtime.Code
