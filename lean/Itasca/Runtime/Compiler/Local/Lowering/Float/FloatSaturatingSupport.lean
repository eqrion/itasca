import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem saturating_float_descriptor {subopcode operation}
    (meaning : Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation) :
    ∃ op : SourceMachine.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
      subopcode.val = (floatOpcode op).val - 256 ∧ operation.instruction = op.source := by
  unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact ⟨.truncate .F32 .I32 .S true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F32 .I32 .U true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F64 .I32 .S true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F64 .I32 .U true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F32 .I64 .S true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F32 .I64 .U true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F64 .I64 .S true,by decide,by assumption,rfl⟩
  · exact ⟨.truncate .F64 .I64 .U true,by decide,by assumption,rfl⟩

theorem wasm1_misc_immediate_false {token bytes}
    (encoded : Wasm1.Immediate 252#u8 token bytes) : False := by
  cases encoded with
  | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
  | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning

end Itasca.Runtime.Compiler

namespace Itasca.Wasm2
open Aeneas Aeneas.Std

end Itasca.Wasm2
