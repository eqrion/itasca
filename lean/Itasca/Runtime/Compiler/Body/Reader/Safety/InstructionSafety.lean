import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.CallbackReadiness
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Safety
import Itasca.Runtime.Compiler.Local.Lowering.Float.SafetyAndEncoding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Reader.Memory.Acceptance
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSafety
import Itasca.Body.Bulk.Step
import Itasca.Runtime.Compiler.Local.Lowering.Literal.Safety
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalSafety
import Itasca.Runtime.Compiler.Local.Relations.Operations.TerminalAndPairSafety
import Itasca.Body.Scalar.Env
import Itasca.Visitor.BodyReplay

/-!
Proofs for Runtime / Compiler / Body / Reader / Safety.

This module collects NumericSafety, ScalarDispatchSafety, SaturatingSafety, ExtendedNumericSafety, ReferenceSafety.
Each section documents its contracts and consumers.
-/

/-! ## NumericSafety -/

section

/-!
Every base integer numeric reader and its concrete compiler callback return normally from a reached callback boundary, including parser and visitor errors.

Main declarations: `compiler_reader_numeric_total` and `compiler_reader_float_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Every base integer numeric reader and its concrete compiler callback return
normally from a reached callback boundary, including parser and visitor errors. -/
theorem compiler_reader_numeric_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := integer_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.Numeric.read.total operation st shape capacity) (by simp)
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
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := float_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.Numeric.read.total operation st shape capacity) (by simp)
  · intro state value read
    obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := float_reader_facts ops compiler state op base
    have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
    subst hook'
    rw [callback]
    exact compiler_float_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits

end Itasca.Compiler

end

/-! ## ScalarDispatchSafety -/

section

/-!
The raw numeric dispatcher returns normally even for unrecognized bytes.

Main declarations: `compiler_reader_numeric_dispatch_total` and `compiler_reader_memory_dispatch_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 8192

private theorem numeric_byte_partition (opcode : U8) (lower : 69 ≤ opcode.val)
    (upper : opcode.val < 192) :
    opcode ∈ integerOpcodes ∨ opcode.val ∈ floatBaseOpcodeValues := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 69 ≤ n at lower
  change n < 192 at upper
  interval_cases n <;> decide +revert

/-- The raw numeric dispatcher returns normally even for unrecognized bytes. -/
theorem compiler_reader_numeric_dispatch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 69 ≤ opcode.val) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases upper : opcode.val < 192
  · rcases numeric_byte_partition opcode lower upper with integer | float
    · obtain ⟨op,eq⟩ := integer_opcode_of_mem integer
      have small := integer_opcode_byte op
      have base : (integerOpcode op).val < 192 := by
        have := congrArg UScalar.val eq
        scalar_tac
      rw [←eq]
      exact compiler_reader_numeric_total ops law compiler st data env ctx ready shape capacity op base
    · obtain ⟨op,base,eq⟩ := float_base_opcode_of_mem float
      rw [←eq]
      exact compiler_reader_float_total ops law compiler st data env ctx ready shape capacity op base
  · have absent : Body.Numeric.opcodeMeaning opcode = none := by
      cases h : Body.Numeric.opcodeMeaning opcode with
      | none => rfl
      | some op =>
        have bounds := Body.Numeric.NumericOp.bounds h
        omega
    rw [code.step.numeric_dispatch _ st data env ctx opcode compiler lower,
      code.step_numeric.unrecognized _ st opcode compiler absent]
    simp

private theorem memory_byte_partition (opcode : U8) (lower : 40 ≤ opcode.val)
    (upper : opcode.val ≤ 62) :
    (∃ op : SourceMachine.Memory.Load, UScalar.cast .U8 (memoryLoadOpcode op) = opcode) ∨
    (∃ op : SourceMachine.Memory.Store, UScalar.cast .U8 (memoryStoreOpcode op) = opcode) := by
  interval_cases h : opcode.val
  · exact Or.inl ⟨.full .I32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .I64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .F32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .F64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .byte .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .byte .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .half .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .half .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .byte .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .byte .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .half .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .half .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .word .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .word .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .I32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .I64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .F32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .F64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I32 .byte, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I32 .half, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .byte, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .half, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .word, (UScalar.eq_equiv _ _).mpr h.symm⟩

/-- Every raw load/store opcode dispatches to a total canonical memory reader. -/
theorem compiler_reader_memory_dispatch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 40 ≤ opcode.val) (upper : opcode.val ≤ 62) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rcases memory_byte_partition opcode lower upper with ⟨op,rfl⟩ | ⟨op,rfl⟩
  · exact compiler_reader_memory_load_total ops law compiler st data env ctx ready shape capacity op
  · exact compiler_reader_memory_store_total ops law compiler st data env ctx ready shape capacity op
end Itasca.Compiler

end

/-! ## SaturatingSafety -/

section

/-!
Prefix decoding, all eight saturating conversions, and rejected subopcodes return normally; successful callbacks establish the observed operand boundary.

Main declarations: `compiler_reader_saturating_dispatch_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

private theorem saturating_descriptor (opcode : U32) (small : opcode.val < 8) :
    ∃ op : SourceMachine.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
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
    (subopcode : U32) (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 252#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_extended.prefixed]
  obtain ⟨result,read,_⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  simp only [Body.prefixedStep,read,bind_ok]
  cases result with
  | Err error => simp
  | Ok pair =>
    obtain ⟨subopcode,next⟩ := pair
    cases meaning : Body.NumericExtensions.saturatingMeaning subopcode with
    | none => simp [meaning]
    | some operation =>
      simp only [meaning]
      have small : subopcode.val < 8 := by
        unfold Body.NumericExtensions.saturatingMeaning at meaning
        split at meaning <;> simp_all
      obtain ⟨op,extension,index⟩ := saturating_descriptor subopcode small
      refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
      · have unary := Body.NumericExtensions.saturating_unary meaning
        have updatedShape : Body.Control.Shape {st with pos := next} := ⟨shape.ordered,shape.bounded⟩
        simpa only [Body.Numeric.read,unary,Bool.false_eq_true,↓reduceIte] using
          WP.spec_mono (Body.Numeric.read.total operation {st with pos := next} updatedShape capacity) (by simp)
      · intro state value converted
        rw [saturating_callback ops compiler state subopcode op extension index]
        exact compiler_float_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Compiler

end

/-! ## ExtendedNumericSafety -/

section

/-!
Sign-extension readers and callbacks return normally from every reached boundary.

Main declarations: `compiler_reader_sign_total` and `compiler_reader_sign_dispatch_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

private theorem sign_callback {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨operation,hook,meaning,rest⟩ := integer_sign_reader_facts ops compiler st op extension
  rw [code.step_extended.sign _ st data env ctx _ operation compiler meaning]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · have unary := (Body.NumericExtensions.sign_properties meaning).1
    simpa only [Body.Numeric.read,unary,Bool.false_eq_true,↓reduceIte] using
      WP.spec_mono (Body.Numeric.read.total operation st shape capacity) (by simp)
  · intro state value read
    rw [sign_callback ops compiler state op extension]
    exact compiler_numeric_total ops law compiler state op ready.codeFits ready.sourceFits ready.coordinateFits

private theorem sign_byte_descriptor (opcode : U8) (lower : 192 ≤ opcode.val)
    (upper : opcode.val ≤ 196) :
    ∃ op : SourceMachine.Numeric.Instruction, 192 ≤ (integerOpcode op).val ∧
      UScalar.cast .U8 (integerOpcode op) = opcode := by
  interval_cases h : opcode.val
  · exact ⟨.unary .I32 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I32 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

theorem compiler_reader_sign_dispatch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 192 ≤ opcode.val) (upper : opcode.val ≤ 196) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  obtain ⟨op,extension,rfl⟩ := sign_byte_descriptor opcode lower upper
  exact compiler_reader_sign_total ops law compiler st data env ctx ready shape capacity op extension
end Itasca.Compiler

end

/-! ## ReferenceSafety -/

section

/-! ## BulkSafety -/

section

/-!
The extracted bulk dispatcher returns for every subopcode and immediate, including reader rejection, allocation rejection and unknown subopcodes.

Main declarations: `compiler_reader_bulk_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- The extracted bulk dispatcher returns for every subopcode and immediate,
including reader rejection, allocation rejection and unknown subopcodes. -/
theorem compiler_reader_bulk_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (opcode : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_bulk (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_bulk.eq_runs]
  unfold bulkStep
  split
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_init.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryInit 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.take_data_index.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.dataDrop 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_copy.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryCopy) 0#u32 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_memory_fill.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.memoryFill) 0#u32 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_init.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableInit 0 0) value.1 value.2
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.take_element.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.elemDrop 0) value.1 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_copy.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableCopy 0 0) value.1 value.2
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_grow.total st data env shape capacity) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableGrow 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_size.total st data env shape capacity) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableSize 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (code.read_table_fill.total st data env shape) (by simp)
    · intro state value read
      exact compiler_stateful_total ops law compiler state (.tableFill 0) value 0#u32
        ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
  · simp
end Itasca.Compiler

end

/-! ## LiteralSafety -/

section

/-!
Normal return of constant and basic scalar reader callbacks.

Main declarations: `compiler_reader_i32_const_total` and `compiler_reader_nop_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_i32_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_i32_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.i32_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_i32_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_i64_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_i64_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.i64_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_i64_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_f32_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_f32_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.f32_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_f32_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_f64_const_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_f64_const]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.f64_const st data shape capacity) (by simp)
  · intro state value read
    exact compiler_on_f64_const_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_drop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_DROP compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_drop]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.drop st shape capacity) (by simp)
  · intro state value read
    exact compiler_on_drop_total ops law compiler state value

theorem compiler_reader_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_select.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.select st shape capacity) (by simp)
  · intro state value read
    exact compiler_select_raw_total ops law compiler state st.vals.val false ready.observed ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_global_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_GET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_global_get.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.global_get st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_global_get_total ops law compiler state value ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_global_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_global_set.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.global_set st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_global_set_total ops law compiler state value st.vals.val ready.observed ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_unreachable_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_unreachable]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact by
      unfold code.read_unreachable
      step with code.mark_unreachable_total st shape
  · intro state value read
    exact compiler_on_unreachable_total ops law compiler state ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_nop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_NOP compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [Visitor.Dispatch.dispatch_nop]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact by simp
  · intro state value read
    exact compiler_on_nop_total ops law compiler state
end Itasca.Compiler

end

/-! ## ReferenceSafety -/

section

/-!
Normal return of reference, typed-select and memory/table metadata reader operations.

Main declarations: `compiler_reader_typed_select_total` and `compiler_reader_memory_grow_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_typed_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 28#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.typed_select]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_typed_select.total st data shape capacity) (by simp)
  · intro state value read
    exact compiler_select_raw_total ops law compiler state st.vals.val true ready.observed
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_table_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 37#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.table_get]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_table_get.total st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.tableGet 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_table_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 38#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.table_set]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_table_set.total st data env shape) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.tableSet 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_null_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 208#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_null]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_null.total st data shape capacity) (by simp)
  · intro state value read
    cases value
    · simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_ref_null.eq,
        runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null.eq,bind_ok,
        Bool.false_eq_true,↓reduceIte,statefulOpcode] using
        compiler_stateful_total ops law compiler state (.refNull .FUNCREF) 0#u32 0#u32
          ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
    · simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_ref_null.eq,
        runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null.eq,bind_ok,
        Bool.false_eq_true,↓reduceIte,statefulOpcode] using
        compiler_stateful_total ops law compiler state (.refNull .EXTERNREF) 1#u32 0#u32
          ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_is_null_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 209#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_is_null]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_is_null.total st shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.refIsNull) 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_ref_func_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 210#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_wasm2.ref_func]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (code.read_ref_func.total st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state (.refFunc 0) value 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_size_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_MEMORY_SIZE compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_memory_size.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.memory_size st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state .memorySize 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_grow_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_MEMORY_GROW compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_memory_grow.dispatch]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.memory_grow st data env shape capacity) (by simp)
  · intro state value read
    exact compiler_stateful_total ops law compiler state .memoryGrow 0#u32 0#u32
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Compiler

end

end
