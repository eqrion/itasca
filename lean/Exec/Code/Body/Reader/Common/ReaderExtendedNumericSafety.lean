import Exec.Code.Body.Reader.Common.ReaderNumericSafety
import Exec.Code.Body.Reader.Common.ReaderSaturating
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem sign_callback {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
    code.visit_sign_extension (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler state (UScalar.cast .U8 (integerOpcode op)) =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 := by
  obtain ⟨operation,hook,_,_,_,_,encoding,callback,_⟩ := integer_sign_reader_facts ops compiler state op extension
  have dispatch := ExtendedNumericHook.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state hook
  simpa only [encoding] using dispatch.trans callback

/-- Sign-extension readers and callbacks return normally from every reached boundary. -/
theorem compiler_reader_sign_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,rest⟩ := integer_sign_reader_facts ops compiler st op extension
  rw [code.step_extended.sign _ st data env ctx _ operation compiler meaning]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · have unary := (Wasm2.NumericExtensions.sign_properties meaning).1
    simpa only [Numeric.read,unary,Bool.false_eq_true,↓reduceIte] using
      WP.spec_mono (Numeric.read.total operation st shape capacity) (by simp)
  · intro state value read
    rw [sign_callback ops compiler state op extension]
    exact compiler_numeric_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits

private theorem sign_byte_descriptor (opcode : U8) (lower : 192 ≤ opcode.val)
    (upper : opcode.val ≤ 196) :
    ∃ op : Abs.Numeric.Instruction, 192 ≤ (integerOpcode op).val ∧
      UScalar.cast .U8 (integerOpcode op) = opcode := by
  interval_cases h : opcode.val
  · exact ⟨.unary .I32 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I32 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

theorem compiler_reader_sign_dispatch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 192 ≤ opcode.val) (upper : opcode.val ≤ 196) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨op,extension,rfl⟩ := sign_byte_descriptor opcode lower upper
  exact compiler_reader_sign_total ops law compiler st data env ctx ready shape capacity op extension
end Itasca.Runtime.Code
