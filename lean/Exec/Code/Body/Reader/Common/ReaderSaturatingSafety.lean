import Exec.Code.Body.Reader.Common.ReaderNumericSafety
import Exec.Code.Body.Reader.Common.ReaderSaturating
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem saturating_descriptor (opcode : U32) (small : opcode.val < 8) :
    ∃ op : Abs.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
      opcode.val = (floatOpcode op).val - 256 := by
  interval_cases h : opcode.val
  · exact ⟨.truncate .F32 .I32 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I32 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I32 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I32 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I64 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I64 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I64 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I64 .U true,by decide,rfl⟩

private theorem saturating_callback {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (subopcode : U32) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (index : subopcode.val = (floatOpcode op).val - 256) :
    code.visit_saturating (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler state subopcode =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 := by
  obtain ⟨sub,operation,hook,subEq,_,_,_,_,_,encoding,callback⟩ :=
    float_saturating_reader_facts ops compiler state op extension
  have eq : sub = subopcode := (UScalar.eq_equiv _ _).mpr (subEq.trans index.symm)
  subst sub
  have dispatch := ExtendedNumericHook.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state hook
  simpa only [encoding] using dispatch.trans callback

/-- Prefix decoding, all eight saturating conversions, and rejected subopcodes
return normally; successful callbacks establish the observed operand boundary. -/
theorem compiler_reader_saturating_dispatch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 252#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_extended.prefixed]
  obtain ⟨result,read,_⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  simp only [Wasm2.prefixedStep,read,bind_ok]
  cases result with
  | Err error => simp
  | Ok pair =>
    obtain ⟨subopcode,next⟩ := pair
    cases meaning : Wasm2.NumericExtensions.saturatingMeaning subopcode with
    | none => simp [meaning]
    | some operation =>
      simp only [meaning]
      have small : subopcode.val < 8 := by
        unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
        split at meaning <;> simp_all
      obtain ⟨op,extension,index⟩ := saturating_descriptor subopcode small
      refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
      · have unary := Wasm2.NumericExtensions.saturating_unary meaning
        have updatedShape : Control.Shape {st with pos := next} := ⟨shape.ordered,shape.bounded⟩
        simpa only [Numeric.read,unary,Bool.false_eq_true,↓reduceIte] using
          WP.spec_mono (Numeric.read.total operation {st with pos := next} updatedShape capacity) (by simp)
      · intro state value converted
        rw [saturating_callback ops compiler state subopcode op extension index]
        exact compiler_float_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Runtime.Code
