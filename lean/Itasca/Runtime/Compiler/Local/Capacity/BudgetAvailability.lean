import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs

/-!
Sections, each formerly its own module: TableGrowth, AuxiliaryGrowth, StatefulAuxiliaryGrowth, BudgetAvailability.
-/

/-! ## TableGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_table_branch_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 2 := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' growth_control_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## AuxiliaryGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Each auxiliary entry is charged to a newly emitted instruction. -/
def AuxiliaryGrowth {A} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after.function.indirect.val.length + before.function.code.val.length ≤
    before.function.indirect.val.length + after.function.code.val.length ∧
  after.function.simd.val.length + before.function.code.val.length ≤
    before.function.simd.val.length + after.function.code.val.length ∧
  after.function.v128_pool.val.length + before.function.code.val.length ≤
    before.function.v128_pool.val.length + after.function.code.val.length

theorem AuxiliaryGrowth.of_tables {A} {before after : runtime.compiler.FunctionCompiler A}
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (code : before.function.code.val.length ≤ after.function.code.val.length) :
    AuxiliaryGrowth before after := by
  have counts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,Prod.mk.injEq] at counts
  unfold AuxiliaryGrowth
  omega

theorem AuxiliaryGrowth.bounded {A} {before after : runtime.compiler.FunctionCompiler A}
    (growth : AuxiliaryGrowth before after)
    (indirect : before.function.indirect.val.length ≤ before.function.code.val.length)
    (simd : before.function.simd.val.length ≤ before.function.code.val.length)
    (pool : before.function.v128_pool.val.length ≤ before.function.code.val.length) :
    after.function.indirect.val.length ≤ after.function.code.val.length ∧
    after.function.simd.val.length ≤ after.function.code.val.length ∧
    after.function.v128_pool.val.length ≤ after.function.code.val.length := by
  unfold AuxiliaryGrowth at growth
  omega

private theorem finish_code_success {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (),after)) :
    after.function.code.val.length = before.function.code.val.length + 1 := by
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) accepted).success
  rw [compiler_observe_code_result ops law middle after state (.Ok ()) rest,
    compiler_emit_code_success ops law before middle instruction emitted]
  simp

open Lean Meta Elab Tactic in
elab "auxiliary_growth_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not named"
  let tac ← match functionName with
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| (have codeEffect := finish_code_success $ops $law _ _ _ _ $h
                 have tables := compiler_finish_op_tables $ops $law _ _ _ _ _ $h
                 have tableCounts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables))
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| (have codeEffect := compiler_observe_code_result $ops $law _ _ _ _ $h
                 have tables := compiler_observe_tables $ops $law _ _ _ _ $h
                 have tableCounts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables))
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| (have codeEffect := compiler_copy_code_mono $ops $law _ _ _ _ _ _ $h
                 have tables := compiler_copy_tables $ops _ _ _ _ _ _ $h
                 have tableCounts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables))
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| (obtain ⟨budget,pairs,effect,appended,_⟩ := compiler_pair_success $ops $law _ _ _ _ _ $h
                 subst_vars))
    | _ => throwError "not helper"
  evalTactic tac

macro "auxiliary_growth_close" : tactic => `(tactic|
  (simp_all [AuxiliaryGrowth,CompilerTables.ofFunction,source_unit_eq]
   try omega))
macro "auxiliary_growth_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; auxiliary_growth_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (auxiliary_growth_effect $h using $ops, $law; auxiliary_growth_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; auxiliary_growth_close)
  | (fail_if_no_progress simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,bind_ok,bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value,called,rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue,secondValue⟩)
     | skip
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     all_goals try auxiliary_growth_effect called using $ops, $law
     all_goals try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

theorem compiler_indirect_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (),after)) :
    AuxiliaryGrowth before after := by
  by_cases live : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b live] at accepted
    unfold indirectCallLowering at accepted
    repeat' auxiliary_growth_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at accepted
    exact .of_tables (compiler_observe_tables ops law before after state (.Ok ()) accepted)
      (compiler_observe_code_mono ops law before after state (.Ok ()) accepted)

end Itasca.Runtime.Compiler

end

/-! ## StatefulAuxiliaryGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_stateful_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    AuxiliaryGrowth before after := by
  by_cases live : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b live] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' auxiliary_growth_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at accepted
    exact .of_tables (compiler_observe_tables ops law before after state (.Ok ()) accepted)
      (compiler_observe_code_mono ops law before after state (.Ok ()) accepted)
end Itasca.Runtime.Compiler

end

/-! ## BudgetAvailability -/

section

/-! Compiler primitives accept independently bounded available resources.
These lemmas do not assume a successful callback or compilation trace. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A remaining instruction budget excludes both resource rejection and checked
arithmetic failure for the actual charge operation. -/
theorem charge_instruction_available {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.instructions.val < budget.limits.max_instructions.val) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ out =>
      out.1 = .Ok () ∧ out.2.instructions.val = budget.instructions.val + 1 ∧
      out.2.limits = budget.limits ∧ out.2.error = budget.error ⦄ := by
  have notFull : ¬ budget.instructions ≥ budget.limits.max_instructions := by scalar_tac
  simp only [runtime.compiler.Budget.charge,notFull,↓reduceIte]
  step as ⟨used,increment⟩
  exact increment

end Itasca.Runtime.Compiler

end
