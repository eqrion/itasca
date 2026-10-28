import Exec.Code.Body.Reader.Table.TableSourceTransferBounds
import Exec.Code.Local.Checking.TableCallbackExitSlots

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Typed labels and a source transfer intervals discharge the actual complete
table callback, including the fallback, scratch clearing, and observation. -/
theorem StructuredCompilerPrefix.br_table_scratch_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget0 : runtime.compiler.Budget A) (buffer : alloc.vec.Vec U32)
    (state : code.OpIterState) (fallback : U32) (view : signature.ResultType)
    (labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes raw = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧
        stack = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops {before with budget := budget0,table_depths := buffer} state fallback view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_table_callback_exit_slots ops law {before with budget := budget0,table_depths := buffer} after state fallback view
    (held.retained rfl le_rfl) _ called
  intro labeled labelCalled live lowered lowerCalled
  obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law {before with budget := budget0,table_depths := buffer} labeled state fallback labelCalled
  subst labeled
  change depths.val = buffer.val++[fallback] at appended
  change before.reachable = true at live
  obtain ⟨stack,input,typedLabels⟩ := labels live
  have layout := (invariant.live live).2.layout
  rw [input] at layout
  have geometry := invariant.table_transfer_geometry live input typedLabels
  apply compiler_lower_table_exit_slots ops law {before with budget,table_depths := depths} lowered ?transfers (layout.capacity live)
    (held.retained rfl le_rfl) lowerCalled
  · intro depth member index frame found position
    change depth ∈ depths.val at member
    rw [appended] at member
    exact geometry depth member index frame found position

end Itasca.Runtime.Code
