import Exec.Code.Body.Reader.Table.TableSourceTransferBounds
import Exec.Code.Local.Checking.TableCallbackInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Typed labels and a source-paid stub budget discharge the actual complete
table callback, including the fallback, scratch clearing, and observation. -/
theorem StructuredCompilerPrefixWithTables.br_table_scratch_open_instructions
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget0 : runtime.compiler.Budget A) (buffer : alloc.vec.Vec U32)
    (state : code.OpIterState) (fallback : U32) (view : signature.ResultType)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (room : before.function.code.val.length+1+2*(buffer.val.length+1) ≤ Usize.max)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes raw = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧
        stack = scope.front++discarded++scope.branchTypes)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops {before with budget := budget0,table_depths := buffer} state fallback view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_table_callback_open_instructions ops law {before with budget := budget0,table_depths := buffer} after state fallback view
    (held.retained rfl rfl) _ called
  intro labeled labelCalled live lowered lowerCalled
  obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law {before with budget := budget0,table_depths := buffer} labeled state fallback labelCalled
  subst labeled
  change depths.val = buffer.val++[fallback] at appended
  change before.reachable = true at live
  obtain ⟨stack,input,typedLabels⟩ := labels live
  have layout := (invariant.live live).2.layout
  rw [input] at layout
  have stagedLayout : CompilerLayout {before with budget,table_depths := depths} (stack++[.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  have geometry := invariant.table_transfer_geometry live input typedLabels
  apply compiler_lower_table_open_instructions ops law _ lowered stack stagedLayout invariant.sources
    ?depths fixups ?room tables coordinate ?nonempty ?transfers (layout.capacity live)
    (held.retained rfl rfl) lowerCalled
  · intro depth member
    change depth ∈ depths.val at member
    rw [appended] at member
    obtain ⟨scope,discarded,selected,targetStack⟩ := typedLabels depth member
    obtain ⟨index,frame,_,_,_,position,_⟩ :=
      invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
    change depth.val < before.frames.val.length
    omega
  · change before.function.code.val.length+1+2*depths.val.length ≤ Usize.max
    rw [appended,List.length_append,List.length_singleton]
    exact room
  · change 0 < depths.val.length
    rw [appended,List.length_append,List.length_singleton]
    omega
  · intro depth member index frame found position
    change depth ∈ depths.val at member
    rw [appended] at member
    exact geometry depth member index frame found position

end Exec.Code
