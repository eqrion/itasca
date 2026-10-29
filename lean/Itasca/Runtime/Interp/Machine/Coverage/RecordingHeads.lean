import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Interp.Machine.Coverage.SupportedHeadCoverage

/-!
The source-event shape retained by recorded code heads.

Main declarations: `RecordingHeads`. A direct consumer is `Integration.Host.HostRecordingSite`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std

class RecordingHeads (emission : ContextEmission) : Prop where
  shape : ∀{C before source emitted after}, emission C before source emitted after → Code.RecordingEmissionShape source emitted

instance (tables : Code.CompilerTables) : RecordingHeads (Code.ExecutableEmission tables) := ⟨Code.ExecutableEmission.recording_shape⟩

private theorem fragment_callTag {code pc next emitted instruction}
    (segment : Code.Segment code pc emitted next)
    (fetched : code[pc]?=some instruction) (nonempty : emitted≠[]) :
    emitted.head?=some instruction := by
  cases emitted with
  | nil => contradiction
  | cons first rest =>
    have fetch := segment.fetch (index:=0) (instruction:=first) rfl
    simp only [Nat.add_zero,fetched,Option.some.injEq] at fetch
    simpa only [List.head?_cons] using congrArg some fetch.symm

/-- A ready source head can fetch a host-capable bytecode only at a direct or
indirect source call. This follows from exact emitted syntax, not a semantic
assumption about the host callback. -/
theorem code_recording_source {emission : ContextEmission} [RecordingHeads emission]
    {C returns locals code jumpTables labels stack op source pc next output instruction}
    (ready : ReadyInstruction op)
    (relation : Code.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (op::source) pc next output)
    (fetched : code[pc]?=some instruction) (calls : Code.callTag instruction≠0) :
    (∃index : U32,op=.CALL (.mk_uN index.val)) ∨ (∃table type : U32,op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)) := by
  cases relation with
  | linear head ordinary fragment rest =>
    have shape := RecordingHeads.shape head
    have nonempty := fun empty => (show False from by
      rcases shape.1 empty with rfl | rfl <;> exact ready)
    have first := fragment_callTag fragment fetched nonempty
    obtain ⟨direct,indirect⟩ := shape.2 _ first
    cases instruction <;> first
      | exact (calls rfl).elim
      | exact (direct _ _ rfl).elim
      | exact Or.inr (indirect _ _ _ rfl)
  | skip forward head rest => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | block => exact ready.elim
  | loop signature head bodyCode rest bounds => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | ifElse signature condition head yesCode skip noCode rest bounds => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | branch lookup live layout fragment remaining scope =>
    have first := fragment_callTag fragment fetched (by unfold Code.branchInstructions; split <;> simp)
    unfold Code.branchInstructions Code.transferInstruction at first
    split at first
    · simp only [List.head?_cons,Option.some.injEq] at first
      subst instruction
      exact (calls rfl).elim
    · split at first <;> (try split at first) <;>
        simp only [List.head?_cons,Option.some.injEq] at first <;>
        subst instruction <;> exact (calls rfl).elim
  | branchIf lookup live layout condition fragment rest =>
    have first := fragment_callTag fragment fetched (by unfold Code.branchIfInstructions; split <;> simp)
    unfold Code.branchIfInstructions at first
    split at first <;> simp only [List.head?_cons,Option.some.injEq] at first <;>
      subst instruction <;> exact (calls rfl).elim
  | call => exact Or.inl ⟨_,rfl⟩
  | unreachable head remaining scope => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | return_ source size head remaining scope => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | branchTable gate table bounds => rw [table.instruction] at fetched; cases fetched; exact (calls rfl).elim
end Itasca.Runtime.Interp.StructuredMachine
