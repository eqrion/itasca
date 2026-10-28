import Itasca.Runtime.Code.Local.Lowering.Simd.SimdStaticTables
import Itasca.Runtime.Code.Local.Capacity.EmissionGrowth
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem emit_auxiliary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.function.simd = before.function.simd ∧
    after.function.v128_pool = before.function.v128_pool ∧
    after.function.indirect = before.function.indirect ∧
    (status = .Ok () → after.function.code.val.length = before.function.code.val.length + 1) := by
  have tables := compiler_emit_tables ops before after instruction status accepted
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (alloc.vec.Vec.eq_iff _ _).mpr
    exact congrArg CompilerTables.simd tables
  · apply (alloc.vec.Vec.eq_iff _ _).mpr
    exact congrArg CompilerTables.constants tables
  · apply (alloc.vec.Vec.eq_iff _ _).mpr
    exact congrArg CompilerTables.indirect tables
  · intro success
    subst status
    simp [compiler_emit_code_success ops law before after instruction accepted]

private theorem observe_auxiliary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.simd = before.function.simd ∧
    after.function.v128_pool = before.function.v128_pool ∧
    after.function.indirect = before.function.indirect ∧
    after.function.code = before.function.code := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  rw [frame]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem push_auxiliary_result {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.Budget.push ops budget before value = .ok (status,afterBudget,after)) :
    after.val.length ≤ before.val.length + 1 := by
  rcases budget_push_code_result ops law budget afterBudget before after value status accepted with same | appended
  · simp [same]
  · simp [appended]

open Lean Meta Elab Tactic in
elab "simd_auxiliary_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| obtain ⟨simdEq, poolEq, indirectEq, codeGrowth⟩ := emit_auxiliary_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| obtain ⟨simdEq, poolEq, indirectEq, codeEq⟩ := observe_auxiliary_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.Budget.push =>
      `(tactic| have pushedGrowth := push_auxiliary_result $ops $law _ _ _ _ _ _ $h)
    | _ => throwError "not an auxiliary-vector helper"
  evalTactic tac

macro "simd_auxiliary_close" : tactic => `(tactic|
  (simp_all only [Prod.mk.injEq, Result.ok.injEq, source_unit_eq]
   try simp_all [show (524#16#uscalar : U16) = 524#u16 from rfl]
   try omega))

macro "simd_auxiliary_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; simd_auxiliary_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (simd_auxiliary_effect $h using $ops, $law; simd_auxiliary_close)
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
     try simd_auxiliary_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

/-- Every accepted SIMD callback emits one instruction. Its immediate record
or vector-constant pool grows by at most one; rejected prefixes are excluded. -/
theorem compiler_simd_auxiliary_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.function.code.val.length = before.function.code.val.length + 1 ∧
    after.function.simd.val.length ≤ before.function.simd.val.length + 1 ∧
    after.function.v128_pool.val.length ≤ before.function.v128_pool.val.length + 1 ∧
    after.function.indirect = before.function.indirect ∧
    (opcode ≠ 524#u16 → after.function.v128_pool = before.function.v128_pool) := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' simd_auxiliary_step accepted using ops, law

/-- Successful live or dormant SIMD dispatch preserves auxiliary-table
headroom relative to actual emitted code. Vector constants use the pool;
all other SIMD instructions preserve that pool exactly. -/
theorem compiler_lower_simd_auxiliary_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length ∧
    after.function.simd.val.length ≤ before.function.simd.val.length +
      (after.function.code.val.length - before.function.code.val.length) ∧
    after.function.v128_pool.val.length ≤ before.function.v128_pool.val.length +
      (after.function.code.val.length - before.function.code.val.length) ∧
    after.function.indirect = before.function.indirect ∧
    (opcode ≠ 524#u16 → after.function.v128_pool = before.function.v128_pool) := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    obtain ⟨code, simd, pool, indirect, poolEq⟩ :=
      compiler_simd_auxiliary_success ops law before after state opcode a bits accepted
    exact ⟨by omega, by omega, by omega, indirect, poolEq⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    obtain ⟨simd, pool, indirect, code⟩ :=
      observe_auxiliary_result ops law before after state (.Ok ()) accepted
    simp [simd, pool, indirect, code]

end Itasca.Runtime.Code
