import Exec.Abs.SimdCumulative
import Exec.Code.Local.Relations.Common.ConsumedPrefix
open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- Structured headers/delimiters and only the plain instructions of the
cumulative instruction family may occur in its flattened source token stream. -/
def SimdCumulativeToken : Token → Prop
  | .plain instruction => Exec.Abs.SimdCumulativeInstr instruction
  | _ => True

theorem Emits.simd_cumulative_tokens {tokens ops} (emitted : Emits tokens ops) :
    Forall Exec.Abs.SimdCumulativeInstr ops → Forall SimdCumulativeToken tokens := by
  induction emitted with
  | nil => simp [Forall]
  | @simple tokens ops token op previous simple ih =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported op (by simp)
    cases simple
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier last
  | @block tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.BLOCK (Control.blockType bt) body) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.block_body last)
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside
  | @loop tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.LOOP (Control.blockType bt) body) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.loop_body last)
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside
  | @ifElse tokens ops yesTokens yes noTokens no bt previous yesCode noCode ih ihYes ihNo =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (Control.blockType bt) yes no) (by simp)
    obtain ⟨yesSupported, noSupported⟩ := Exec.Abs.SimdCumulativeInstr.if_bodies last
    have yesInside := ihYes yesSupported
    have noInside := ihNo noSupported
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken, and_assoc] using ⟨earlier, yesInside, noInside⟩
  | @ifEnd tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (Control.blockType bt) body []) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.if_bodies last).1
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside

theorem BodyTokens.simd_cumulative_tokens {tokens ops} (body : BodyTokens tokens ops)
    (supported : Forall Exec.Abs.SimdCumulativeInstr ops) : Forall SimdCumulativeToken tokens := by
  obtain ⟨inner, rfl, emitted⟩ := body
  have inside := emitted.simd_cumulative_tokens supported
  simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using inside
/-- A retained unfinished reader prefix selects a supported token from the
original complete cumulative body, independently of opcode-specific parser facts. -/
theorem BodyEncoding.next_simd_cumulative_token {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.SimdCumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    ∃ token next, At data position token next ∧ SimdCumulativeToken token := by
  obtain ⟨allTokens, finish, complete, endPosition, spelling⟩ := encoded
  obtain ⟨token, next, suffix, split, atToken, rest⟩ :=
    before.next_of_prefix complete (by omega)
  refine ⟨token, next, atToken, spelling.simd_cumulative_tokens supported token ?_⟩
  rw [split]
  simp

end Itasca.Wasm1

namespace Itasca.Wasm2

/-- Structured headers/delimiters and only the plain instructions of the
cumulative instruction family may occur in its flattened source token stream. -/
def SimdCumulativeToken : Token → Prop
  | .plain instruction => Exec.Abs.SimdCumulativeInstr instruction
  | _ => True

theorem Emits.simd_cumulative_tokens {tokens ops} (emitted : Emits tokens ops) :
    Forall Exec.Abs.SimdCumulativeInstr ops → Forall SimdCumulativeToken tokens := by
  induction emitted with
  | nil => simp [Forall]
  | @simple tokens ops token op previous simple ih =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported op (by simp)
    cases simple
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier last
  | @block tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.BLOCK (blockType bt) body) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.block_body last)
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside
  | @loop tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.LOOP (blockType bt) body) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.loop_body last)
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside
  | @ifElse tokens ops yesTokens yes noTokens no bt previous yesCode noCode ih ihYes ihNo =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (blockType bt) yes no) (by simp)
    obtain ⟨yesSupported, noSupported⟩ := Exec.Abs.SimdCumulativeInstr.if_bodies last
    have yesInside := ihYes yesSupported
    have noInside := ihNo noSupported
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken, and_assoc] using ⟨earlier, yesInside, noInside⟩
  | @ifEnd tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (blockType bt) body []) (by simp)
    have inside := ihBody (Exec.Abs.SimdCumulativeInstr.if_bodies last).1
    simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using And.intro earlier inside

theorem BodyTokens.simd_cumulative_tokens {tokens ops} (body : BodyTokens tokens ops)
    (supported : Forall Exec.Abs.SimdCumulativeInstr ops) : Forall SimdCumulativeToken tokens := by
  obtain ⟨inner, rfl, emitted⟩ := body
  have inside := emitted.simd_cumulative_tokens supported
  simpa [Forall, or_imp, forall_and, SimdCumulativeToken] using inside
/-- A retained unfinished reader prefix selects a supported token from the
original complete cumulative body, independently of opcode-specific parser facts. -/
theorem BodyEncoding.next_simd_cumulative_token {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.SimdCumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    ∃ token next, At data position token next ∧ SimdCumulativeToken token := by
  obtain ⟨allTokens, finish, complete, endPosition, spelling⟩ := encoded
  obtain ⟨token, next, suffix, split, atToken, rest⟩ :=
    before.next_of_prefix complete (by omega)
  refine ⟨token, next, atToken, spelling.simd_cumulative_tokens supported token ?_⟩
  rw [split]
  simp

end Itasca.Wasm2
