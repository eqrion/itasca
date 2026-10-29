import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Stateful.Descriptor
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatSaturatingSupport

/-!
The extended-opcode classification for saturating conversions and the ten bulk operations.

Main declarations: `CumulativeMiscOpcode`. A direct consumer is `Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

def CumulativeMiscOpcode (subopcode : U32) : Prop :=
  (∃ op : Abs.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
    subopcode.val = (floatOpcode op).val - 256) ∨
  subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17]

theorem misc_cumulative_immediate {token bytes}
    (encoded : Wasm2.Immediate 252#u8 token bytes) :
    ∃ subopcode prefixBytes suffix, bytes = prefixBytes ++ suffix ∧
      Leb128.Encoding prefixBytes subopcode.val ∧ CumulativeMiscOpcode subopcode := by
  cases encoded with
  | plain h => exact False.elim (wasm1_misc_immediate_false h)
  | signExtension opcode operation meaning => simp [Wasm2.NumericExtensions.signMeaning] at meaning
  | saturating subopcode operation meaning leb =>
    obtain ⟨op,extension,equal,_⟩ := saturating_float_descriptor meaning
    exact ⟨subopcode,_,[],by simp,leb,Or.inl ⟨op,extension,equal⟩⟩
  | reference h => cases h
  | bulk subopcode prefixEncoding h =>
    refine ⟨subopcode,_,_,rfl,prefixEncoding,Or.inr ?_⟩
    cases h <;> simp
end Itasca.Runtime.Code

namespace Itasca.Wasm2
open Aeneas Aeneas.Std

theorem At.cumulative_misc {data start token finish}
    (encoded : At data start token finish)
    (next : Usize) (advance : next.val = start.val + 1) (inbounds : start.val < data.length)
    (byte : data.val[start.val]'inbounds = 252#u8) :
    ∃ subopcode endPosition, Leb128.Decoded data next subopcode endPosition ∧
      Itasca.Runtime.Code.CumulativeMiscOpcode subopcode := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have first := congrArg List.head? span.suffix
  have equal : opcode = 252#u8 := by
    have equal : data.val[start.val] = opcode := by
      simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using first
    exact equal.symm.trans byte
  subst opcode
  obtain ⟨subopcode,prefixBytes,suffix,rfl,leb,allowed⟩ := Itasca.Runtime.Code.misc_cumulative_immediate grammar
  have split : Wasm1.BytesAt data start ([252#u8] ++ (prefixBytes ++ suffix)) finish := span
  obtain ⟨middle,head,tail⟩ := split.split
  have middleEq : middle = next := by
    apply UScalar.eq_of_val_eq
    have position := head.length
    simpa only [List.length_singleton,advance] using position
  subst middle
  obtain ⟨endPosition,prefixAt,suffixAt⟩ := tail.split
  exact ⟨subopcode,endPosition,⟨prefixBytes,prefixAt.suffix,prefixAt.length,prefixAt.bound,leb⟩,allowed⟩

end Itasca.Wasm2
