import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatSafety
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts

/-!
Every base integer numeric reader and its concrete compiler callback return normally from a reached callback boundary, including parser and visitor errors.

Main declarations: `compiler_reader_numeric_total` and `compiler_reader_float_total`. A direct consumer is `Compiler.Body.Reader.Safety.ExtendedNumericSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every base integer numeric reader and its concrete compiler callback return
normally from a reached callback boundary, including parser and visitor errors. -/
theorem compiler_reader_numeric_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192) :
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256) :
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

end Itasca.Runtime.Compiler
