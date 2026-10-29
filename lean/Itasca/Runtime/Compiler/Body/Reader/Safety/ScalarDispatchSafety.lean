import Itasca.Runtime.Compiler.Body.Reader.Safety.NumericSafety
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemorySafety
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode

/-!
The raw numeric dispatcher returns normally even for unrecognized bytes.

Main declarations: `compiler_reader_numeric_dispatch_total` and `compiler_reader_memory_dispatch_total`. A direct consumer is `Compiler.Body.Reader.Safety.ScalarSafety`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 8000000
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 69 ≤ opcode.val) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases upper : opcode.val < 192
  · rcases numeric_byte_partition opcode lower upper with integer | float
    · obtain ⟨op,eq⟩ := integer_opcode_of_mem integer
      have small := integerOpcode_byte op
      have base : (integerOpcode op).val < 192 := by
        have := congrArg UScalar.val eq
        scalar_tac
      rw [←eq]
      exact compiler_reader_numeric_total ops law compiler st data env ctx ready shape capacity op base
    · obtain ⟨op,base,eq⟩ := float_base_opcode_of_mem float
      rw [←eq]
      exact compiler_reader_float_total ops law compiler st data env ctx ready shape capacity op base
  · have absent : Numeric.opcodeMeaning opcode = none := by
      cases h : Numeric.opcodeMeaning opcode with
      | none => rfl
      | some op =>
        have bounds := Numeric.NumericOp.bounds h
        omega
    rw [code.step.numeric_dispatch _ st data env ctx opcode compiler lower,
      code.step_numeric.unrecognized _ st opcode compiler absent]
    simp

private theorem memory_byte_partition (opcode : U8) (lower : 40 ≤ opcode.val)
    (upper : opcode.val ≤ 62) :
    (∃ op : Abs.Memory.Load, UScalar.cast .U8 (memoryLoadOpcode op) = opcode) ∨
    (∃ op : Abs.Memory.Store, UScalar.cast .U8 (memoryStoreOpcode op) = opcode) := by
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (lower : 40 ≤ opcode.val) (upper : opcode.val ≤ 62) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rcases memory_byte_partition opcode lower upper with ⟨op,rfl⟩ | ⟨op,rfl⟩
  · exact compiler_reader_memory_load_total ops law compiler st data env ctx ready shape capacity op
  · exact compiler_reader_memory_store_total ops law compiler st data env ctx ready shape capacity op
end Itasca.Runtime.Code
