import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ScalarAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Reader.Safety.ScalarDispatchSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.ExtendedNumericSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.SaturatingSafety

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem source_numeric_byte_partition (opcode : U8) (lower : 69 ≤ opcode.val)
    (upper : opcode.val < 192) :
    opcode ∈ integerOpcodes ∨ opcode.val ∈ floatBaseOpcodeValues := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 69 ≤ n at lower
  change n < 192 at upper
  interval_cases n <;> decide +revert

theorem source_memory_byte_partition (opcode : U8) (lower : 40 ≤ opcode.val)
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

theorem source_sign_byte_descriptor (opcode : U8) (lower : 192 ≤ opcode.val)
    (upper : opcode.val ≤ 196) :
    ∃ op : SourceMachine.Numeric.Instruction, 192 ≤ (integerOpcode op).val ∧
      UScalar.cast .U8 (integerOpcode op) = opcode := by
  interval_cases h : opcode.val
  · exact ⟨.unary .I32 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I32 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

theorem source_saturating_descriptor (opcode : U32) (small : opcode.val < 8) :
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

end Itasca.Runtime.Compiler
