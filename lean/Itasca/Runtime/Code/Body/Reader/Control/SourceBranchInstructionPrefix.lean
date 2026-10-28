import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderBranchLayout
import Itasca.Runtime.Code.Body.Control.Table.StructuredBranchIfLayout
import Itasca.Runtime.Code.Local.Callbacks.Common.FixupBudget
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableArguments
import Itasca.Runtime.Code.Local.Checking.BranchCallbackInstructionPrefix
import Itasca.Runtime.Code.Local.Checking.ConditionalLoopInstructionPrefix
import Itasca.Runtime.Code.Local.Checking.LoopBranchInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A source loop frame points to its retained entry hook. -/
theorem FrameScope.loop_instruction_target {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {locals scope frame} (shape : FrameScope locals compiler scope frame) (loop : frame.kind = .Loop) :
    frame.start_pc.val ≤ compiler.function.code.length := by
  have kind := shape.kind
  have start := shape.start
  have entry := shape.entryBound
  cases form : scope.form <;> simp_all [ScopeForm.kind,SourceScope.frameStart]

/-- Typed source label selection supplies every transfer and target premise
needed by the actual unconditional branch callback. -/
theorem StructuredCompilerPrefix.br_open_instructions
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (label : before.reachable = true → ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes raw = scope.front++discarded++scope.branchTypes)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_callback_open_instructions ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,selected,input⟩ := label live
  obtain ⟨index,frame,source,found,frameAt,shape,height,sourceAt,sourceWidth⟩ :=
    invariant.branch_layout live depth.val scope selected discarded input
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have room := invariant.codeBudget
  have codeFits : before.function.code.val.length+2 ≤ Usize.max := by
    have bound := invariant.codeBudget.code_capacity sourceBound
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  have offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max := by
    rw [invariant.sources]
    exact codeFits
  by_cases loop : frame.kind = .Loop
  · have width' : frame.params.val = slots scope.branchTypes := by simpa [frameBranchWidth,loop] using width
    exact compiler_branch_loop_open_instructions ops law before middle frame index depth source 0#u32
      found frameAt loop (by change source.val+frame.params.val+0 = before.height.val; omega)
      order (by omega) (shape.loop_instruction_target loop) codeFits offsetsFit coordinate held branch
  · have width' : frame.results.val = slots scope.branchTypes := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    exact compiler_branch_forward_open_instructions ops law before middle frame index depth source 0#u32
      found frameAt loop (by change source.val+frame.results.val+0 = before.height.val; omega)
      order (by omega) (fixups.lookup found (by omega)) codeFits offsetsFit coordinate held branch

/-- Conditional source label selection additionally bounds the consumed i32
selector and the local continuation around an actual transfer. -/
theorem StructuredCompilerPrefix.br_if_open_instructions
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
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_if_callback_open_instructions ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,stack,selected,input,targetStack⟩ := label live
  obtain ⟨index,frame,source,condition,found,frameAt,shape,height,sourceAt,sourceWidth,conditionAt,conditionSlot⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have layout := (invariant.live live).2.layout.height
  have localsEq := (invariant.live live).2.localsEq
  rw [input] at layout
  simp only [slots_append,slots,show Itasca.Runtime.Code.width (.I32 : valtype) = 1 from rfl,localsEq] at layout
  have test : condition.val+1 ≤ before.function.slot_count.val := by omega
  have room := invariant.codeBudget
  have resumeFits : before.function.code.val.length+3 < 2^32 := by
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  let resume : U32 := UScalar.ofNatCore (before.function.code.val.length+3) resumeFits
  by_cases loop : frame.kind = .Loop
  · have width' : frame.params.val = slots scope.branchTypes := by simpa [frameBranchWidth,loop] using width
    exact compiler_branch_if_loop_open_instructions ops law before middle frame index depth source condition resume
      found frameAt loop (by omega) conditionAt rfl order (by omega) test
      (shape.loop_instruction_target loop) held branch
  · have width' : frame.results.val = slots scope.branchTypes := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    exact compiler_branch_if_forward_open_instructions ops law before middle frame index depth source condition resume
      found frameAt loop (by omega) conditionAt rfl order (by omega) test held branch

end Itasca.Runtime.Code
