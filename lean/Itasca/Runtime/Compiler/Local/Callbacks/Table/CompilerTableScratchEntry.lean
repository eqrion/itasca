import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables

/-!
Sections, each formerly its own module: FixupTablePreservation, CompilerTableScratchEntry.
-/

/-! ## FixupTablePreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem TableTargetsBuilt.fixup_budget {A}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets}
    (built : TableTargetsBuilt before after depths targets)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  induction built with
  | nil => exact budget
  | cons _ _ _ _ _ _ effect rest ih => exact ih (effect.fixup_budget budget)

theorem compiler_lower_table_fixup_budget {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨start,len,selector,emitted,targets,_,_,_,emission,built,_⟩ :=
    compiler_lower_table_production ops law before after accepted
  obtain ⟨allocation,code,sources,rfl,codeEq,_⟩ := emission
  apply built.fixup_budget
  apply budget.mono
  simp [codeEq]

theorem compiler_br_table_fixup_budget {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops before state fallback types =
      .ok (.Ok (),after)) : FixupBudget after.frames.val after.function.code.val.length := by
  by_cases live : before.reachable = true
  · obtain ⟨allocation,depths,lowered,cleared,_,lower,_,observed⟩ :=
      compiler_br_table_success ops law before after state fallback types live accepted
    have kept := compiler_lower_table_fixup_budget ops law {before with budget := allocation, table_depths := depths}
      lowered budget lower
    exact FixupBudget.ordinary (before := {lowered with reachable := false, table_depths := cleared}) kept
      (compiler_observe_ordinary_result ops law _ after state (.Ok ()) observed)
      (compiler_observe_code_mono ops law _ after state (.Ok ()) observed)
  · have dead : before.reachable = false := by simpa using live
    obtain ⟨_,code,_,frames,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types dead accepted
    simpa [code,frames] using budget
end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchEntry -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve branch-table scratch and code buffers. -/
def CompilerTableEntryMetadata {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.table_depths, after.function.jump_tables, after.function.code) =
    (before.table_depths, before.function.jump_tables, before.function.code)

theorem CompilerTableEntryMetadata.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerTableEntryMetadata before middle) (second : CompilerTableEntryMetadata middle after) :
    CompilerTableEntryMetadata before after := Eq.trans second first




theorem compiler_function_start_table_entry_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    CompilerTableEntryMetadata before after := by
  have frame := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.inv
    ops before after ctx typeIndex start finish status accepted
  unfold CompilerTableEntryMetadata
  rw [frame]

theorem compiler_new_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      CompilerTableBoundary out ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.new.eq, WP.spec_ok]
  exact CompilerTableBoundary.empty rfl rfl

theorem compiler_function_start_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (boundary : CompilerTableBoundary before)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    CompilerTableBoundary after := by
  have fields := compiler_function_start_table_entry_metadata ops law before after ctx typeIndex start finish status accepted
  simp only [CompilerTableEntryMetadata, Prod.mk.injEq] at fields
  exact boundary.preserved fields.1 fields.2.1 (by rw [fields.2.2])

end Itasca.Runtime.Compiler

end
