import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableProduction
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableDead
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
