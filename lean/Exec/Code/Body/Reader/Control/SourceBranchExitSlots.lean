import Exec.Code.Body.Reader.Control.SourceBranchInstructionPrefix
import Exec.Code.Local.Checking.BranchCallbackExitSlots

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Typed source label selection supplies every transfer and target premise
needed by the actual unconditional branch callback. -/
theorem StructuredCompilerPrefix.br_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (label : before.reachable = true → ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes raw = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_callback_exit_slots ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,selected,input⟩ := label live
  obtain ⟨index,frame,source,found,frameAt,shape,height,sourceAt,sourceWidth⟩ :=
    invariant.branch_layout live depth.val scope selected discarded input
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  apply compiler_branch_exit_slots ops law before middle index frame depth source 0#u32 found frameAt
    (by change source.val+(frameBranchWidth frame).val+0 = before.height.val; omega) order
    (by omega) held branch

/-- Conditional source label selection additionally bounds the consumed i32
selector and the local continuation around an actual transfer. -/
theorem StructuredCompilerPrefix.br_if_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (label : before.reachable = true → ∃ scope discarded stack,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes raw = stack++[.I32] ∧ stack = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_if_callback_exit_slots ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,stack,selected,input,targetStack⟩ := label live
  obtain ⟨index,frame,source,condition,found,frameAt,shape,height,sourceAt,sourceWidth,conditionAt,conditionSlot⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have room := invariant.codeBudget
  have resumeFits : before.function.code.val.length+3 < 2^32 := by
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  let resume : U32 := UScalar.ofNatCore (before.function.code.val.length+3) resumeFits
  exact compiler_branch_if_exit_slots ops law before middle index frame depth source condition resume
    found frameAt (by omega) conditionAt rfl order (by omega) held branch

end Exec.Code
