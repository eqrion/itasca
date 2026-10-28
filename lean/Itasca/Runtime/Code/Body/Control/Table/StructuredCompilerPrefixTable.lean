import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalBranchTable
import Itasca.Runtime.Code.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableCallbackLayout
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableScopeFrames
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Code.Local.Capacity.BranchTableGrowth
import Itasca.Runtime.Code.Local.Relations.Table.TableSources
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- An actual successful live table callback advances the indexed compiler
certificate once, retaining every dispatch arm under all future fixup plans. -/
theorem StructuredCompilerPrefix.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables : List U32} {emit types functions returns locals parents current raw position nextRaw}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (depths : List U32) (fallback : U32) (blockTypes : signature.ResultType)
    (stack : List valtype) (stackEq : Sequence.stackTypes raw = stack ++ [.I32])
    (inputs : TableOperandScopes (parents ++ [current]) stack (depths ++ [fallback]))
    (buffer : before.table_depths.val = depths)
    (dominance : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (futureTables : List U32) (tableEq : jumpTables = after.function.jump_tables.val ++ futureTables)
    (gate : ∀ selector start len, emit (stack ++ [.I32])
      (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))
      [.JumpTable selector start len] stack)
    (consumed : position + depths.length + 2 ≤ state.pos.val)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback blockTypes = .ok (.Ok (),after)) :
    StructuredCompilerPrefix jumpTables emit initial after types functions returns locals parents
      (current.advance (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))) nextRaw state.pos.val := by
  obtain ⟨entered, original⟩ := invariant.live live
  have retained : StructuredUniversalPrefix jumpTables emit before types functions returns locals
      parents current (stack ++ [.I32]) := stackEq ▸ original
  have fixed := compiler_br_table_fixed ops law before after state fallback blockTypes live accepted
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, fixed.stable.fields.2.2.2.2.1]
    exact retained.localsEq
  obtain ⟨frames, dormant, sites⟩ := compiler_br_table_scope_frames ops law before after state fallback blockTypes
    invariant.frames invariant.entryChain entered retained.sites (by rw [fixed.controls]) live accepted
  obtain ⟨sources, cursor⟩ := compiler_br_table_sources ops law before after state fallback blockTypes accepted
  obtain ⟨budget, collected, start, len, selector, emitted, lowered, targets,
    collectedEq, startEq, lenEq, emission, built, codeEq, framesEq, tableAppend, count, clear, dead, header⟩ :=
    compiler_br_table_production ops law before after state fallback blockTypes live accepted
  have framesLength : after.frames.val.length = before.frames.val.length := by
    rw [framesEq, built.frame_length]
    obtain ⟨_, _, _, emittedEq, _, _⟩ := emission
    rw [emittedEq]
  have completion : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
      ∃ previous selector start len suffix,
        FramePlans before.function.code.val.length locals before.frames.val (label :: labels) previous ∧
        resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ suffix ∧
        BranchTableLayout jumpTables locals (label :: labels) stack (resolvedCode after.function.code.val groups)
          (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
          before.function.code.val.length after.function.code.val.length selector start len ∧
        before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    intro label labels groups plans shape parentShapes
    have shapes : List.Forall₂ ScopeLabel (parents ++ [current]).reverse (label :: labels) := by
      simpa using List.Forall₂.cons shape parentShapes
    obtain ⟨previous, start, len, selector, previousPlans, table, header, _, _, extra, code⟩ :=
      compiler_br_table_layout_prefix ops law before after state fallback blockTypes locals stack
        (parents ++ [current]) (label :: labels) depths groups buffer retained.layout retained.localsEq
        (invariant.frames.frames.imp (fun _ _ p => p.toScopeFrameShape)) shapes inputs dominance retained.sites
        plans live accepted
    refine ⟨previous, selector, start, len, .JumpTable selector start len :: extra, previousPlans, code, ?_, header⟩
    simpa only [tableEq] using table.append_tables futureTables
  have terminal := retained.branch_table _ _ localsEq sites gate completion
  have arms := invariant.arms.resolved_append (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))
    (by
      intro label labels groups plans shape parentShapes
      obtain ⟨previous, selector, start, len, suffix, previousPlans, code, _, _⟩ :=
        completion label labels groups plans shape parentShapes
      exact ⟨previous, suffix, previousPlans, code⟩)
  have growth := compiler_br_table_code_growth ops law before after state fallback blockTypes live accepted
  rw [buffer] at growth
  refine ⟨invariant.metadata.trans fixed.stable, frames.advance _, invariant.entryChain.advance _, dormant,
    invariant.conditions.advance _, (by intro contradiction; simp [dead] at contradiction),
    .terminal dead entered terminal, arms, sources.aligned invariant.sources, ?_, ?_, ?_⟩
  · exact invariant.codeBudget.table growth (by omega)
  · exact (invariant.controlBudget.transport (by rw [fixed.controls]) (Nat.le_of_eq framesLength)).advance (by omega)
  · rw [cursor]
end Itasca.Runtime.Code
