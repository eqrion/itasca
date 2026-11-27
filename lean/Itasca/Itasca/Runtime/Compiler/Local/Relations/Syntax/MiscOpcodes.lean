import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Float.InstructionChecks

/-!
The extended-opcode classification for saturating conversions and the ten bulk operations.

Main declarations: `MiscOpcode`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

def MiscOpcode (subopcode : U32) : Prop :=
  (∃ op : SourceMachine.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
    subopcode.val = (floatOpcode op).val - 256) ∨
  subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17]

theorem misc_immediate {token bytes}
    (encoded : Body.Immediate 252#u8 token bytes) :
    ∃ subopcode prefixBytes suffix, bytes = prefixBytes ++ suffix ∧
      Binary.Leb128.Encoding prefixBytes subopcode.val ∧ MiscOpcode subopcode := by
  cases encoded with
  | plain h => exact False.elim (scalar_misc_immediate_false h)
  | signExtensionInstruction opcode source meaning =>
    change Body.NumericExtensions.signInstruction 252#u8 = some source at meaning
    rw [Body.NumericExtensions.signInstruction_eq] at meaning
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp meaning
    simp [Body.NumericExtensions.signMeaning] at decoded
  | saturatingInstruction subopcode source meaning leb =>
    change Body.NumericExtensions.saturatingInstruction subopcode = some source at meaning
    rw [Body.NumericExtensions.saturatingInstruction_eq] at meaning
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp meaning
    obtain ⟨op,extension,equal,_⟩ := saturating_float_descriptor decoded
    exact ⟨subopcode,_,[],by simp,leb,Or.inl ⟨op,extension,equal⟩⟩
  | reference h => cases h
  | bulk subopcode prefixEncoding h =>
    refine ⟨subopcode,_,_,rfl,prefixEncoding,Or.inr ?_⟩
    cases h <;> decide
end Itasca.Compiler

namespace Itasca.Body
open Aeneas Aeneas.Std

theorem At.misc_opcode {data start token finish}
    (encoded : At data start token finish)
    (next : Usize) (advance : next.val = start.val + 1) (inbounds : start.val < data.length)
    (byte : data.val[start.val]'inbounds = 252#u8) :
    ∃ subopcode endPosition, Binary.Leb128.Decoded data next subopcode endPosition ∧
      Itasca.Compiler.MiscOpcode subopcode := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have first := congrArg List.head? span.suffix
  have equal : opcode = 252#u8 := by
    have equal : data.val[start.val] = opcode := by
      simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using first
    exact equal.symm.trans byte
  subst opcode
  obtain ⟨subopcode,prefixBytes,suffix,rfl,leb,allowed⟩ := Itasca.Compiler.misc_immediate grammar
  have split : Body.Scalar.BytesAt data start ([252#u8] ++ (prefixBytes ++ suffix)) finish := span
  obtain ⟨middle,head,tail⟩ := split.split
  have middleEq : middle = next := by
    apply UScalar.eq_of_val_eq
    have position := head.length
    simpa only [List.length_singleton,advance] using position
  subst middle
  obtain ⟨endPosition,prefixAt,suffixAt⟩ := tail.split
  exact ⟨subopcode,endPosition,⟨prefixBytes,prefixAt.suffix,prefixAt.length,prefixAt.bound,leb⟩,allowed⟩

end Itasca.Body

namespace Itasca.Body
open Aeneas Aeneas.Std

/-- The complete independent body encoding determines every accepted misc
subopcode without an additional source-subset premise. -/
theorem BodyEncoding.next_misc {data body tokens position}
    (encoded : BodyEncoding data body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length)
    (next : Usize) (advance : next.val = position.val + 1)
    (byte : data.val[position.val]'remaining = 252#u8) :
    ∃ subopcode endPosition, Binary.Leb128.Decoded data next subopcode endPosition ∧
      Itasca.Compiler.MiscOpcode subopcode := by
  obtain ⟨allTokens,finish,complete,endPosition,spelling⟩ := encoded
  obtain ⟨token,nextToken,suffix,split,atToken,rest⟩ := before.next_of_prefix complete (by omega)
  exact atToken.misc_opcode next advance remaining byte
end Itasca.Body
