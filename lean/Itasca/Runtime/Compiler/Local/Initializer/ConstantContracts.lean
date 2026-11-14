import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit

/-! Canonical contracts for synthetic initializer emission and constants.
Normal errors retain their actual intermediate budget and vector states. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Synthetic emission first charges one instruction, then attempts its append. -/
inductive InitializerEmitEffect {A : Type} (ops : runtime.platform.Alloc A)
    (beforeBudget : runtime.compiler.Budget A) (before : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr) : core.result.Result Unit Itasca.error.VisitError →
    runtime.compiler.Budget A → alloc.vec.Vec runtime.bytecode.Instr → Prop where
  | rejected {error budget}
      (charged : runtime.compiler.Budget.charge ops beforeBudget .Instructions = .ok (.Err error, budget)) :
      InitializerEmitEffect ops beforeBudget before instruction (.Err error) budget before
  | pushed {chargedBudget status budget code}
      (charged : runtime.compiler.Budget.charge ops beforeBudget .Instructions = .ok (.Ok (), chargedBudget))
      (pushed : runtime.compiler.Budget.push ops chargedBudget before instruction = .ok (status, budget, code)) :
      InitializerEmitEffect ops beforeBudget before instruction status budget code

theorem _root_.Itasca.runtime.compiler.initialize.emit.inv {A : Type}
    (ops : runtime.platform.Alloc A) (beforeBudget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.emit ops beforeBudget before instruction = .ok (status, afterBudget, after)) :
    InitializerEmitEffect ops beforeBudget before instruction status afterBudget after := by
  unfold runtime.compiler.initialize.emit at called
  obtain ⟨⟨answer, chargedBudget⟩, charged, tail⟩ := bind_ok_inv _ _ _ called
  cases answer with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .rejected charged
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    exact .pushed charged tail

theorem InitializerEmitEffect.code {A : Type} {ops : runtime.platform.Alloc A}
    {beforeBudget afterBudget : runtime.compiler.Budget A}
    {before after : alloc.vec.Vec runtime.bytecode.Instr} {instruction status}
    (effect : InitializerEmitEffect ops beforeBudget before instruction status afterBudget after)
    (law : Platform.AllocCorrect ops) :
    after.val = before.val ∨ after.val = before.val ++ [instruction] := by
  cases effect with
  | rejected charged => exact Or.inl rfl
  | pushed charged pushed => exact budget_push_code_result ops law _ _ _ _ _ _ pushed

theorem InitializerEmitEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {beforeBudget afterBudget : runtime.compiler.Budget A}
    {before after : alloc.vec.Vec runtime.bytecode.Instr} {instruction}
    (effect : InitializerEmitEffect ops beforeBudget before instruction (.Ok ()) afterBudget after)
    (law : Platform.AllocCorrect ops) : after.val = before.val ++ [instruction] := by
  cases effect with
  | pushed charged pushed => exact (budget_push_success ops law _ _ _ _ _ pushed).2

@[step] theorem _root_.Itasca.runtime.compiler.initialize.emit.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr) (fits : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨status, chargedBudget, limits, count⟩
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (budget_push ops law chargedBudget code instruction fits)
    intro output post
    trivial

@[step] theorem _root_.Itasca.runtime.compiler.initialize.emit.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (fits : code.length < Usize.max) (request : code.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ ∃ used, afterBudget = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ∧ after.val = code.val ++ [instruction] ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction_available_exact ops budget room as ⟨status, charged, accepted, used, frame, count⟩
  rw [accepted, frame]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_mono (budget_push_available ops bound available {budget with instructions := used} code instruction fits request)
  rintro ⟨status, afterBudget, after⟩ ⟨accepted, budgetEq, appended⟩
  exact ⟨accepted, used, budgetEq, count, appended⟩

/-- Every normal constant compilation preserves the precise completed stages. -/
inductive InitializerConstantEffect {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) (before : runtime.bytecode.CompiledFunction)
    (ty : Itasca.wasm_types.ValueType) (dst : U32) : Itasca.wasm_types.ConstExpr →
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.Budget A →
    runtime.bytecode.CompiledFunction → Prop where
  | scalar {expr instruction status afterBudget code}
      (instructionTyped : ConstantInstruction before dst expr ty instruction)
      (emitted : runtime.compiler.initialize.emit ops budget before.code instruction =
        .ok (status, afterBudget, code)) :
      InitializerConstantEffect ops budget before ty dst expr status afterBudget {before with code}
  | indexRejected {lo hi error}
      (indexed : runtime.compiler.bounded_index (alloc.vec.Vec.len before.v128_pool) = .ok (.Err error)) :
      InitializerConstantEffect ops budget before ty dst (.V128 lo hi) (.Err error) budget before
  | poolRejected {lo hi index shifted error afterBudget pool}
      (indexed : runtime.compiler.bounded_index (alloc.vec.Vec.len before.v128_pool) = .ok (.Ok index))
      (shiftedEq : ((UScalar.cast .U128 hi) <<< 64#i32) = .ok shifted)
      (pushed : runtime.compiler.Budget.push ops budget before.v128_pool
        ((UScalar.cast .U128 lo) ||| shifted) = .ok (.Err error, afterBudget, pool)) :
      InitializerConstantEffect ops budget before ty dst (.V128 lo hi) (.Err error) afterBudget
        {before with v128_pool := pool}
  | vector {lo hi index shifted pushedBudget pool status afterBudget code}
      (indexed : runtime.compiler.bounded_index (alloc.vec.Vec.len before.v128_pool) = .ok (.Ok index))
      (shiftedEq : ((UScalar.cast .U128 hi) <<< 64#i32) = .ok shifted)
      (pushed : runtime.compiler.Budget.push ops budget before.v128_pool
        ((UScalar.cast .U128 lo) ||| shifted) = .ok (.Ok (), pushedBudget, pool))
      (emitted : runtime.compiler.initialize.emit ops pushedBudget before.code (.ConstV128 dst index) =
        .ok (status, afterBudget, code)) :
      InitializerConstantEffect ops budget before ty dst (.V128 lo hi) status afterBudget
        {before with code, v128_pool := pool}

private theorem constant_scalar_effect {A : Type} (ops : runtime.platform.Alloc A)
    (budget afterBudget : runtime.compiler.Budget A) (before after : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (instructionTyped : ConstantInstruction before dst expr ty instruction)
    (called : (do
      let (result, nextBudget, code) ← runtime.compiler.initialize.emit ops budget before.code instruction
      Result.ok (result, nextBudget, {before with code})) = .ok (status, afterBudget, after)) :
    InitializerConstantEffect ops budget before ty dst expr status afterBudget after := by
  obtain ⟨⟨result, nextBudget, code⟩, emitted, tail⟩ := bind_ok_inv _ _ _ called
  simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
  obtain ⟨rfl, rfl, rfl⟩ := tail
  exact .scalar instructionTyped emitted

theorem _root_.Itasca.runtime.compiler.initialize.constant.inv {A : Type}
    (ops : runtime.platform.Alloc A) (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.constant ops budget before expr ty dst = .ok (status, afterBudget, after)) :
    InitializerConstantEffect ops budget before ty dst expr status afterBudget after := by
  cases expr with
  | I32 value =>
    simp only [runtime.compiler.initialize.constant, lift, bind_ok] at called
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.i32 value ty) called
  | I64 value =>
    simp only [runtime.compiler.initialize.constant, lift, bind_ok] at called
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.i64 value ty) called
  | F32 bits =>
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.f32 bits ty) called
  | F64 bits =>
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.f64 bits ty) called
  | RefNull elem =>
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.refNull ty elem) called
  | RefFunc index =>
    exact constant_scalar_effect ops budget afterBudget before after _ ty dst _ status
      (.refFunc ty index) called
  | GlobalGet index =>
    cases ty <;> simp only [runtime.compiler.initialize.constant, bind_ok] at called
    all_goals apply constant_scalar_effect ops budget afterBudget before after _ _ dst _ status
    all_goals first
      | exact ConstantInstruction.globalVector index
      | exact ConstantInstruction.global _ index (by intro impossible; cases impossible)
      | exact called
  | V128 lo hi =>
    unfold runtime.compiler.initialize.constant at called
    obtain ⟨indexedResult, indexed, tail⟩ := bind_ok_inv _ _ _ called
    cases indexedResult with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .indexRejected indexed
    | Ok index =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok] at tail
      obtain ⟨shifted, shiftedEq, tail⟩ := bind_ok_inv _ _ _ tail
      obtain ⟨⟨pushedResult, pushedBudget, pool⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
      cases pushedResult with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .poolRejected indexed shiftedEq pushed
      | Ok unitValue =>
        cases unitValue
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
        obtain ⟨⟨emittedResult, emittedBudget, code⟩, emitted, tail⟩ := bind_ok_inv _ _ _ tail
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .vector indexed shiftedEq pushed emitted

def ConstantLowered (before after : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32) : Prop :=
  ∃ code pool instruction,
    after = { before with code, v128_pool := pool } ∧
    code.val = before.code.val ++ [instruction] ∧ ConstantInstruction after dst expr ty instruction


theorem InitializerConstantEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {budget afterBudget : runtime.compiler.Budget A} {before after : runtime.bytecode.CompiledFunction}
    {expr ty dst status}
    (effect : InitializerConstantEffect ops budget before ty dst expr status afterBudget after) :
    after = {before with code := after.code, v128_pool := after.v128_pool} := by
  cases effect <;> rfl

theorem InitializerConstantEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {budget afterBudget : runtime.compiler.Budget A} {before after : runtime.bytecode.CompiledFunction}
    {expr ty dst status}
    (effect : InitializerConstantEffect ops budget before ty dst expr status afterBudget after)
    (law : Platform.AllocCorrect ops) :
    after.code.val.length ≤ before.code.val.length + 1 ∧
    after.v128_pool.val.length ≤ before.v128_pool.val.length + 1 := by
  cases effect with
  | scalar instructionTyped emitted =>
    have code := (runtime.compiler.initialize.emit.inv ops _ _ _ _ _ _ emitted).code law
    rcases code with code | code <;> simp only [code, List.length_append, List.length_singleton] <;> omega
  | indexRejected indexed => exact ⟨by omega, by omega⟩
  | poolRejected indexed shiftedEq pushed =>
    have pool := budget_push_code_result ops law _ _ _ _ _ _ pushed
    rcases pool with pool | pool <;> simp only [pool, List.length_append, List.length_singleton] <;> omega
  | vector indexed shiftedEq pushed emitted =>
    have pool := budget_push_code_result ops law _ _ _ _ _ _ pushed
    have code := (runtime.compiler.initialize.emit.inv ops _ _ _ _ _ _ emitted).code law
    rcases pool with pool | pool <;> rcases code with code | code <;>
      simp only [pool, code, List.length_append, List.length_singleton] <;> omega

theorem InitializerConstantEffect.pool_of_nonvector {A : Type} {ops : runtime.platform.Alloc A}
    {budget afterBudget : runtime.compiler.Budget A} {before after : runtime.bytecode.CompiledFunction}
    {expr ty dst status}
    (effect : InitializerConstantEffect ops budget before ty dst expr status afterBudget after)
    (nonvector : ∀ lo hi, expr ≠ .V128 lo hi) : after.v128_pool = before.v128_pool := by
  cases effect with
  | scalar instructionTyped emitted => rfl
  | indexRejected indexed => rfl
  | poolRejected indexed shiftedEq pushed => exact False.elim (nonvector _ _ rfl)
  | vector indexed shiftedEq pushed emitted => exact False.elim (nonvector _ _ rfl)

private theorem initializer_packed_eq (lo hi : U64) (shifted : U128)
    (shiftedEq : ((UScalar.cast .U128 hi) <<< 64#i32) = .ok shifted) :
    (UScalar.cast .U128 lo) ||| shifted = initializerBits lo hi := by
  have shiftedSpec := U128.ShiftLeft_IScalar_spec (UScalar.cast .U128 hi) 64#i32
    (by scalar_tac) (by scalar_tac)
  rw [shiftedEq] at shiftedSpec
  simp only [WP.spec_ok] at shiftedSpec
  apply U128.bv_eq_imp_eq
  exact congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) shiftedSpec.2

theorem InitializerConstantEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {budget afterBudget : runtime.compiler.Budget A} {before after : runtime.bytecode.CompiledFunction}
    {expr ty dst}
    (effect : InitializerConstantEffect ops budget before ty dst expr (.Ok ()) afterBudget after)
    (law : Platform.AllocCorrect ops) : ConstantLowered before after expr ty dst := by
  cases effect with
  | scalar instructionTyped emitted =>
    have code := (runtime.compiler.initialize.emit.inv ops _ _ _ _ _ _ emitted).success law
    exact ⟨_, _, _, rfl, code, instructionTyped.change_code rfl⟩
  | @vector lo hi index shifted pushedBudget pool status afterBudget code indexed shiftedEq pushed emitted =>
    have codeEq := (runtime.compiler.initialize.emit.inv ops _ _ _ _ _ _ emitted).success law
    have poolEq := (budget_push_success ops law _ _ _ _ _ pushed).2
    have indexedSpec := bounded_index (alloc.vec.Vec.len before.v128_pool)
    rw [indexed] at indexedSpec
    simp only [WP.spec_ok] at indexedSpec
    have indexEq := indexedSpec index rfl
    have packed := initializer_packed_eq lo hi shifted shiftedEq
    refine ⟨_, _, _, rfl, codeEq, ConstantInstruction.v128 lo hi ty index ?_⟩
    rw [poolEq, packed]
    have indexLength : index.val = before.v128_pool.val.length := indexEq
    rw [indexLength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

@[step] theorem _root_.Itasca.runtime.compiler.initialize.constant.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ _ => True ⦄ := by
  cases expr <;> unfold runtime.compiler.initialize.constant
  all_goals repeat' first
    | (step with runtime.compiler.initialize.emit.total ops law _ _ _ codeFits)
    | (step with budget_push ops law _ _ _ poolFits)
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | split
    | step

@[step] theorem _root_.Itasca.runtime.compiler.initialize.constant.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (codeFits : function.code.length < Usize.max) (codeRequest : function.code.length + 1 ≤ bound)
    (poolReady : ∀ lo hi, expr = .V128 lo hi →
      function.v128_pool.length < Usize.max ∧ function.v128_pool.length ≤ U32.max ∧
      function.v128_pool.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ ∃ used, afterBudget = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ∧ ConstantLowered function after expr ty dst ⦄ := by
  cases expr with
  | V128 lo hi =>
    obtain ⟨poolFits, poolIndex, poolRequest⟩ := poolReady lo hi rfl
    unfold runtime.compiler.initialize.constant
    step with bounded_index_available (alloc.vec.Vec.len function.v128_pool) poolIndex
      as ⟨indexedResult, index, indexed, indexEq⟩
    rw [indexed]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨low, lowEq⟩
    step as ⟨high, highEq⟩
    step as ⟨shifted, shiftEq, shiftBits⟩
    step as ⟨word, wordEq, wordBits⟩
    step with budget_push_available ops bound available budget function.v128_pool word poolFits poolRequest
      as ⟨status, nextBudget, pool, accepted, budgetEq, appended⟩
    subst status nextBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with runtime.compiler.initialize.emit.available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status, afterBudget, code, accepted, used, frame, count, codeEq⟩
    refine ⟨accepted, used, frame, count, code, pool, _, rfl, codeEq, .v128 lo hi ty index ?_⟩
    have packed : word = initializerBits lo hi := by
      subst low high
      apply U128.bv_eq_imp_eq
      exact wordBits.trans (congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) shiftBits)
    rw [appended, packed]
    have indexLength : index.val = function.v128_pool.val.length := indexEq
    rw [indexLength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  | GlobalGet index =>
    cases ty <;> simp only [runtime.compiler.initialize.constant, bind_ok]
    all_goals
      step with runtime.compiler.initialize.emit.available ops bound available budget function.code _ room codeFits codeRequest
        as ⟨status, afterBudget, code, accepted, used, frame, count, codeEq⟩
      refine ⟨accepted, used, frame, count, code, function.v128_pool, _, rfl, codeEq, ?_⟩
      first | exact .globalVector index | exact .global _ index (by intro impossible; cases impossible)
  | I32 value | I64 value | F32 value | F64 value | RefNull value | RefFunc value =>
    simp only [runtime.compiler.initialize.constant, lift, bind_ok]
    step with runtime.compiler.initialize.emit.available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status, afterBudget, code, accepted, used, frame, count, codeEq⟩
    refine ⟨accepted, used, frame, count, code, function.v128_pool, _, rfl, codeEq, ?_⟩
    first | exact .i32 value ty | exact .i64 value ty | exact .f32 value ty | exact .f64 value ty
          | exact .refNull ty value | exact .refFunc ty value


end Itasca.Runtime.Compiler
