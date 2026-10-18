import Exec.Code.Local.Lowering.Float.FloatCoreOpcodes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem saturating_float_descriptor {subopcode operation}
    (meaning : Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation) :
    ∃ op : Abs.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
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

theorem misc_float_immediate {token bytes}
    (encoded : Wasm2.Immediate 252#u8 token bytes) (supported : Wasm2.FloatCoreToken token) :
    ∃ subopcode operation, Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation ∧
      Leb128.Encoding bytes subopcode.val ∧ token = .plain operation.instruction := by
  cases encoded with
  | plain h => exact False.elim (wasm1_misc_immediate_false h)
  | signExtension opcode operation meaning => simp [Wasm2.NumericExtensions.signMeaning] at meaning
  | saturating subopcode operation meaning leb => exact ⟨subopcode,operation,meaning,leb,rfl⟩
  | reference h => cases h
  | bulk subopcode prefixEncoding h => cases h <;> have head := float_core_head supported <;> contradiction
end Exec.Code

namespace Itasca.Wasm2
open Aeneas Aeneas.Std

theorem At.float_saturating {data start token finish}
    (encoded : At data start token finish) (supported : FloatCoreToken token)
    (next : Usize) (advance : next.val = start.val + 1) (inbounds : start.val < data.length)
    (byte : data.val[start.val]'inbounds = 252#u8) :
    ∃ op : Exec.Abs.Float.Instruction, ∃ subopcode : U32,
      256 ≤ (Exec.Code.floatOpcode op).val ∧
      subopcode.val = (Exec.Code.floatOpcode op).val - 256 ∧
      Leb128.Decoded data next subopcode finish := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have first := congrArg List.head? span.suffix
  have equal : opcode = 252#u8 := by
    have equal : data.val[start.val] = opcode := by
      simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using first
    exact equal.symm.trans byte
  subst opcode
  obtain ⟨subopcode,operation,meaning,leb,_⟩ := Exec.Code.misc_float_immediate grammar supported
  obtain ⟨op,extension,subopcodeEq,_⟩ := Exec.Code.saturating_float_descriptor meaning
  have split : Wasm1.BytesAt data start ([252#u8] ++ immediate) finish := span
  obtain ⟨middle,head,tail⟩ := split.split
  have middleEq : middle = next := by
    apply UScalar.eq_of_val_eq
    have position := head.length
    simpa only [List.length_singleton,advance] using position
  subst middle
  exact ⟨op,subopcode,extension,subopcodeEq,immediate,tail.suffix,tail.length,tail.bound,leb⟩

theorem BodyEncoding.next_float_saturating {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.FloatCoreInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length)
    (next : Usize) (advance : next.val = position.val + 1)
    (byte : data.val[position.val]'remaining = 252#u8) :
    ∃ op : Exec.Abs.Float.Instruction, ∃ subopcode : U32, ∃ finish : Usize,
      256 ≤ (Exec.Code.floatOpcode op).val ∧
      subopcode.val = (Exec.Code.floatOpcode op).val - 256 ∧
      Leb128.Decoded data next subopcode finish := by
  obtain ⟨token,finish,atToken,allowed⟩ := encoded.next_float_core_token supported before remaining
  obtain ⟨op,subopcode,extension,subopcodeEq,decoded⟩ := atToken.float_saturating allowed next advance remaining byte
  exact ⟨op,subopcode,finish,extension,subopcodeEq,decoded⟩
end Itasca.Wasm2
