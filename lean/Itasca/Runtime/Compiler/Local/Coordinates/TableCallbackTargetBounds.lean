import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneTactic
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessEmit
import Itasca.Runtime.Compiler.Local.Source.JumpTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects

/-!
Branch-table target bounds from strict branch-code growth through the target loop and callback. The result bounds every published jump-table target.
-/

/-! ## Branch Code Strict -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- A successful actual emission extends the instruction vector strictly. -/
theorem compiler_emit_code_strict_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status,after)) :
    status = .Ok () → before.function.code.val.length < after.function.code.val.length := by
  intro success
  subst status
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := compiler_emit_success ops law before after instruction called
  simp only [appended,List.length_append,List.length_singleton]
  omega

open Lean Meta Elab Tactic in
elab "strict_code_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_,lhs,_) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.emit then
    evalTactic (← `(tactic| have strictGrowth := compiler_emit_code_strict_result $ops $law _ _ _ _ $h))
  evalTactic (← `(tactic| code_mono_effect $h using $ops, $law))

macro "strict_code_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; code_mono_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (strict_code_effect $h using $ops, $law; code_mono_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; code_mono_close)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try strict_code_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)


/-- A successful actual branch always emits at least one control instruction,
including loop targets and copies elided by the compiler. -/
theorem compiler_branch_code_strict {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    before.function.code.val.length < after.function.code.val.length := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch,Bool.false_eq_true,ite_false,ite_true] at called <;>
    repeat' strict_code_step called using ops, law

end Itasca.Runtime.Code

end

/-! ## Table Target Bounds -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A table stub records its PC before lowering its branch. Actual branch code
then grows strictly, putting the recorded target inside the resulting vector. -/
theorem compiler_table_branch_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : JumpTableBounds before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨target,budget,table,position,appended,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  have growth := compiler_branch_code_strict ops law staged after depth 1#u32 false branch
  have tables := congrArg CompilerTables.jumpTables (compiler_branch_tables ops law staged after depth 1#u32 false branch)
  change after.function.jump_tables.val = table.val at tables
  intro entry member
  rw [tables,appended] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with prior | rfl
  · exact (held entry prior).trans (by simpa only [staged] using growth)
  · simpa only [position,staged] using growth

/-- Every actual branch in the finite lowering loop retains bounded targets. -/
theorem TableBranchRun.jumpTableBounds {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) (held : JumpTableBounds before) :
    JumpTableBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inbounds called rest ih =>
    let depth := before.table_depths.val[index.val]
    exact ih (compiler_table_branch_target_bounds ops law before middle index depth
      (List.getElem?_eq_getElem inbounds) held called)

/-- The actual dispatch emission and complete stub loop establish all jump-table
bounds without assuming loop acceptance or a completed code certificate. -/
theorem compiler_lower_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : JumpTableBounds before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  exact run.jumpTableBounds law (emission.jumpTableBounds held)

end Itasca.Runtime.Code

end

/-! ## Table Callback Target Bounds -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Streamed labels retain all jump-table targets and code. -/
theorem compiler_table_label_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : JumpTableBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  simpa only [JumpTableBounds,frame] using held

/-- The actual final branch-table callback retains all jump-target bounds. -/
theorem compiler_br_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : JumpTableBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before labeled state fallback labelCalled
    have coordinates : JumpTableBounds labeled := by simpa only [JumpTableBounds,frame] using held
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        have loweredCoordinates := compiler_lower_table_target_bounds ops law labeled lowered coordinates lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_jump_table_bounds ops law {lowered with reachable := false,table_depths := cleared} after state
          (by simpa only [JumpTableBounds] using loweredCoordinates)
          observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_jump_table_bounds ops law {labeled with table_depths := cleared} after state
        (by simpa only [JumpTableBounds] using coordinates) observed

end Itasca.Runtime.Code

end
