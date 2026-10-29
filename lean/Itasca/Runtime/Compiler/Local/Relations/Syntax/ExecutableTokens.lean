import Itasca.Runtime.SourceMachine.BinaryInstr
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix

/-!
Structured headers/delimiters and only the plain instructions of the complete executable instruction family may occur in its flattened source token stream.

Main declarations: `ExecutableToken`. A direct consumer is `Compiler.Local.Relations.Syntax.ReaderOpcode`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Structured headers/delimiters and only the plain instructions of the
complete executable instruction family may occur in its flattened source token stream. -/
def ExecutableToken : Token → Prop
  | .plain instruction => Itasca.Runtime.Abs.BinaryInstr instruction
  | _ => True

theorem Emits.executable_tokens {tokens ops} (emitted : Emits tokens ops) :
    Forall Itasca.Runtime.Abs.BinaryInstr ops → Forall ExecutableToken tokens := by
  induction emitted with
  | nil => simp [Forall]
  | @simple tokens ops token op previous simple ih =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported op (by simp)
    cases simple
    simpa [Forall, or_imp, forall_and, ExecutableToken] using And.intro earlier last
  | @block tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.BLOCK (blockType bt) body) (by simp)
    have inside := ihBody (Itasca.Runtime.Abs.BinaryInstr.block_body last)
    simpa [Forall, or_imp, forall_and, ExecutableToken] using And.intro earlier inside
  | @loop tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.LOOP (blockType bt) body) (by simp)
    have inside := ihBody (Itasca.Runtime.Abs.BinaryInstr.loop_body last)
    simpa [Forall, or_imp, forall_and, ExecutableToken] using And.intro earlier inside
  | @ifElse tokens ops yesTokens yes noTokens no bt previous yesCode noCode ih ihYes ihNo =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (blockType bt) yes no) (by simp)
    obtain ⟨yesSupported, noSupported⟩ := Itasca.Runtime.Abs.BinaryInstr.if_bodies last
    have yesInside := ihYes yesSupported
    have noInside := ihNo noSupported
    simpa [Forall, or_imp, forall_and, ExecutableToken, and_assoc] using ⟨earlier, yesInside, noInside⟩
  | @ifEnd tokens ops bodyTokens body bt previous inner ih ihBody =>
    intro supported
    have earlier := ih (fun instruction member => supported instruction (List.mem_append_left _ member))
    have last := supported (.IFELSE (blockType bt) body []) (by simp)
    have inside := ihBody (Itasca.Runtime.Abs.BinaryInstr.if_bodies last).1
    simpa [Forall, or_imp, forall_and, ExecutableToken] using And.intro earlier inside

theorem BodyTokens.executable_tokens {tokens ops} (body : BodyTokens tokens ops)
    (supported : Forall Itasca.Runtime.Abs.BinaryInstr ops) : Forall ExecutableToken tokens := by
  obtain ⟨inner, rfl, emitted⟩ := body
  have inside := emitted.executable_tokens supported
  simpa [Forall, or_imp, forall_and, ExecutableToken] using inside
/-- A retained unfinished reader prefix selects a supported token from the
original complete executable body, independently of opcode-specific parser facts. -/
theorem BodyEncoding.next_executable_token {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Itasca.Runtime.Abs.BinaryInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    ∃ token next, At data position token next ∧ ExecutableToken token := by
  obtain ⟨allTokens, finish, complete, endPosition, spelling⟩ := encoded
  obtain ⟨token, next, suffix, split, atToken, rest⟩ :=
    before.next_of_prefix complete (by omega)
  refine ⟨token, next, atToken, spelling.executable_tokens supported token ?_⟩
  rw [split]
  simp

end Itasca.Wasm2
