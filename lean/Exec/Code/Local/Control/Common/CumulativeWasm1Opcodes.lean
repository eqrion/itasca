import Exec.Code.Local.Control.Common.CumulativeOpcodes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem wasm1_stateful_extension_impossible {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes)
    (extension : opcode.val ∈ [37,38,208,209,210]) : False := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at extension
  rcases extension with h | h | h | h | h
  · have equal : opcode = 37#u8 := UScalar.eq_of_val_eq h
    subst opcode
    cases encoded with
    | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
    | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning
  · have equal : opcode = 38#u8 := UScalar.eq_of_val_eq h
    subst opcode
    cases encoded with
    | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
    | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning
  · have equal : opcode = 208#u8 := UScalar.eq_of_val_eq h
    subst opcode
    cases encoded with
    | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
    | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning
  · have equal : opcode = 209#u8 := UScalar.eq_of_val_eq h
    subst opcode
    cases encoded with
    | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
    | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning
  · have equal : opcode = 210#u8 := UScalar.eq_of_val_eq h
    subst opcode
    cases encoded with
    | numeric opcode operation meaning => simp [Numeric.opcodeMeaning] at meaning
    | memory opcode operation arg meaning => simp [MemoryMeaning.opcodeMeaning] at meaning
end Exec.Code

namespace Itasca.Wasm1
open Aeneas Aeneas.Std

theorem At.cumulative_wasm1_opcode {data start token next}
    (encoded : At data start token next) (supported : CumulativeToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[start.val] ∨ data.val[start.val].val ∈ [63,64] ∨ data.val[start.val] = 17#u8 := by
  have excluded : ¬data.val[start.val].val ∈ [37,38,208,209,210] := by
    intro extension
    obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
    have head := congrArg List.head? span.suffix
    have equal : data.val[start.val] = opcode := by
      simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using head
    rw [equal] at extension
    exact Exec.Code.wasm1_stateful_extension_impossible grammar extension
  rcases encoded.cumulative_opcode supported inbounds with old | stateful | indirect
  · exact .inl old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at stateful
    rcases stateful with h | h | h | h | h | h | h
    · exact False.elim (excluded (by simp [h]))
    · exact False.elim (excluded (by simp [h]))
    · exact .inr (.inl (by simp [h]))
    · exact .inr (.inl (by simp [h]))
    · exact False.elim (excluded (by simp [h]))
    · exact False.elim (excluded (by simp [h]))
    · exact False.elim (excluded (by simp [h]))

  · exact .inr (.inr indirect)

theorem BodyEncoding.next_cumulative_wasm1_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.CumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[position.val] ∨ data.val[position.val].val ∈ [63,64] ∨ data.val[position.val] = 17#u8 := by
  obtain ⟨token,next,atToken,allowed⟩ := encoded.next_cumulative_token supported before remaining
  exact atToken.cumulative_wasm1_opcode allowed remaining
end Itasca.Wasm1
