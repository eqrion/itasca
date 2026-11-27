import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Module.Const.Parser

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects ExpressionContracts, ElementLoopContracts.
Each section documents its contracts and consumers.
-/

/-! ## ExpressionContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects ConstantContracts, ExpressionContracts.
Each section documents its contracts and consumers.
-/

/-! ## ConstantContracts -/

section

/-! Canonical contracts for synthetic initializer emission and constants.
Normal errors retain their actual intermediate budget and vector states. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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

end Itasca.Compiler

end

/-! ## ExpressionContracts -/

section

open Itasca.Representation

/-!
# Constant-expression compilation

Independent source initializer forms construct expression compilation with the required result width. Vector literals require a vector result slot; other forms retain their own typing evidence.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

def initializerSeed (ty : Itasca.wasm_types.ValueType) : runtime.bytecode.CompiledFunction :=
  { locals := alloc.vec.Vec.new _, local_slots := 0#u32, param_slots := 0#u32,
    slot_count := initializerWidth ty, max_stack := 0#usize, code := alloc.vec.Vec.new _,
    jump_tables := alloc.vec.Vec.new _, v128_pool := alloc.vec.Vec.new _,
    indirect := alloc.vec.Vec.new _, simd := alloc.vec.Vec.new _, source_offsets := alloc.vec.Vec.new _,
    controls := alloc.vec.Vec.new _, type_index := 0#u32, body_start := 0#usize, body_end := 0#usize }

theorem initializer_synthetic (ty : Itasca.wasm_types.ValueType) :
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) (initializerWidth ty) =
      .ok (initializerSeed ty) := rfl

private theorem slots_fit_zero (function : runtime.bytecode.CompiledFunction) (count : U32)
    (bounded : count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count = .ok true := by
  have below : 0#u32 ≤ function.slot_count := by scalar_tac
  simp only [runtime.bytecode.CompiledFunction.slots_fit,if_pos below]
  have check : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count
      ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos below]
    step as ⟨left,equal⟩
    have fits : count ≤ left := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists check
  exact actual

/-- The only extra width condition is independently visible in the source:
a vector literal requires a vector result slot. Other constant-expression
forms fit the width selected from their result type. -/
theorem initial_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : function.slot_count = initializerWidth ty)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slots_fit_zero
    rw [capacity]
    cases ty <;> decide
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slots_fit_zero
    simp [capacity,same,initializerWidth]
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  have poolBound : UScalar.cast .Usize pool < alloc.vec.Vec.len function.v128_pool := by scalar_tac
  simpa [lift] using inside

/-- Exact initializer code and source metadata imply the actual publication
checker accepts. Component checker success is derived here, not assumed. -/
theorem initializer_well_formed (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (shape : InitializerCode function expr ty)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (offsets : function.source_offsets.val = []) (jumps : function.jump_tables.val = [])
    (controls : function.controls.val = [])
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  obtain ⟨instruction,lowered,code⟩ := shape.code
  have length : function.code.length = 2 := by simp [alloc.vec.Vec.length,code]
  apply well_formed_synthetic_accepts function start finish (by omega) offsets
    (by rw [shape.localSlots,shape.capacity]; cases ty <;> decide)
    (by rw [shape.paramSlots,shape.localSlots]) 0#u32 (initializerWidth ty)
  · simp [length,code]
  · intro j bounded
    rw [length] at bounded
    have first := initial_instruction_accepts function expr ty instruction lowered shape.capacity vector
    have returned : runtime.bytecode.CompiledFunction.instruction_valid function
        (.Return 0#u32 (initializerWidth ty)) = .ok true := by
      simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
      exact slots_fit_zero function (initializerWidth ty) (by rw [shape.capacity])
    interval_cases j <;> simpa [code] using (by assumption)
  · simp [jumps]
  · simp [controls]

/-- Successful constant and return emission, prior to the publication checker. -/
structure InitializerExpressionPrefix {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) where
  constantBudget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  returnBudget : runtime.compiler.Budget A
  code : alloc.vec.Vec runtime.bytecode.Instr
  constantCalled : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
    .ok (.Ok (), constantBudget, function)
  returnCalled : runtime.compiler.initialize.emit ops constantBudget function.code
    (.Return 0#u32 (initializerWidth ty)) = .ok (.Ok (), returnBudget, code)

def InitializerExpressionPrefix.result {A : Type} {ops : runtime.platform.Alloc A}
    {budget : runtime.compiler.Budget A} {expr ty} (stages : InitializerExpressionPrefix ops budget expr ty) :
    runtime.bytecode.CompiledFunction := {stages.function with code := stages.code}

/-- Exact normal-return stages of initializer expression publication. -/
inductive InitializerExpressionEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) :
    core.result.Result Usize Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop where
  | constantRejected {error afterBudget function}
      (called : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
        .ok (.Err error, afterBudget, function)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) before afterBudget
  | returnRejected {error constantBudget function afterBudget code}
      (constantCalled : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
        .ok (.Ok (), constantBudget, function))
      (returnCalled : runtime.compiler.initialize.emit ops constantBudget function.code
        (.Return 0#u32 (initializerWidth ty)) = .ok (.Err error, afterBudget, code)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) before afterBudget
  | checkerRejected (stages : InitializerExpressionPrefix ops budget expr ty)
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok false) :
      InitializerExpressionEffect ops before budget expr ty (.Err .OutOfMemory) before stages.returnBudget
  | published (stages : InitializerExpressionPrefix ops budget expr ty) {afterBudget functions}
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok true)
      (pushed : runtime.compiler.Budget.push ops stages.returnBudget before.functions stages.result =
        .ok (.Ok (), afterBudget, functions)) :
      InitializerExpressionEffect ops before budget expr ty (.Ok (alloc.vec.Vec.len before.functions))
        {before with functions} afterBudget
  | publicationRejected (stages : InitializerExpressionPrefix ops budget expr ty) {error afterBudget functions}
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok true)
      (pushed : runtime.compiler.Budget.push ops stages.returnBudget before.functions stages.result =
        .ok (.Err error, afterBudget, functions)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) {before with functions} afterBudget

 theorem _root_.Itasca.runtime.compiler.initialize.expression.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (status : core.result.Result Usize Itasca.error.VisitError)
    (called : runtime.compiler.initialize.expression ops before budget expr ty = .ok (status, after, afterBudget)) :
    InitializerExpressionEffect ops before budget expr ty status after afterBudget := by
  unfold runtime.compiler.initialize.expression at called
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok] at called
  obtain ⟨⟨constantStatus, constantBudget, function⟩, constantCalled, tail⟩ := bind_ok_inv _ _ _ called
  cases constantStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .constantRejected constantCalled
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨returnStatus, returnBudget, code⟩, returnCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases returnStatus with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .returnRejected constantCalled returnCalled
    | Ok unitValue =>
      cases unitValue
      let stages : InitializerExpressionPrefix ops budget expr ty :=
        ⟨constantBudget, function, returnBudget, code, constantCalled, returnCalled⟩
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      obtain ⟨valid, checked, tail⟩ := bind_ok_inv _ _ _ tail
      cases valid with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .checkerRejected stages checked
      | true =>
        simp only [ite_true] at tail
        obtain ⟨⟨pushedStatus, pushedBudget, functions⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
        cases pushedStatus with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .publicationRejected stages checked pushed
        | Ok unitValue =>
          cases unitValue
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            bind_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .published stages checked pushed

theorem InitializerExpressionPrefix.certified {A : Type} {ops : runtime.platform.Alloc A}
    {budget : runtime.compiler.Budget A} {expr ty}
    (stages : InitializerExpressionPrefix ops budget expr ty) (law : Platform.AllocCorrect ops) :
    InitializerCode stages.result expr ty := by
  have lowered := (runtime.compiler.initialize.constant.inv ops budget stages.constantBudget
    (initializerSeed ty) stages.function expr ty 0#u32 (.Ok ()) stages.constantCalled).success law
  have returned := (runtime.compiler.initialize.emit.inv ops stages.constantBudget stages.returnBudget
    stages.function.code stages.code (.Return 0#u32 (initializerWidth ty)) (.Ok ()) stages.returnCalled).success law
  obtain ⟨code, pool, instruction, frame, appended, certified⟩ := lowered
  have finalCertified : ConstantInstruction stages.result 0#u32 expr ty instruction :=
    ConstantInstruction.change_code (after := stages.result) certified rfl
  have finalCode : stages.result.code.val = [instruction, .Return 0#u32 (initializerWidth ty)] := by
    change stages.code.val = [instruction, .Return 0#u32 (initializerWidth ty)]
    rw [returned, frame]
    have codeEq : code.val = [instruction] := by
      simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using appended
    rw [codeEq]
    rfl

  refine ⟨⟨instruction, finalCertified, finalCode⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [InitializerExpressionPrefix.result, frame, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]

theorem InitializerExpressionEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty status}
    (effect : InitializerExpressionEffect ops before budget expr ty status after afterBudget) :
    after = {before with functions := after.functions} := by
  cases effect <;> rfl

theorem InitializerExpressionEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty status}
    (effect : InitializerExpressionEffect ops before budget expr ty status after afterBudget)
    (law : Platform.AllocCorrect ops) : after.functions.val.length ≤ before.functions.val.length + 1 := by
  cases effect with
  | constantRejected called => omega
  | returnRejected constantCalled returnCalled => omega
  | checkerRejected stages checked => omega
  | published stages checked pushed | publicationRejected stages checked pushed =>
    have changed := budget_push_code_result ops law _ _ _ _ _ _ pushed
    rcases changed with same | appended
    · simp only [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem InitializerExpressionEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty index}
    (effect : InitializerExpressionEffect ops before budget expr ty (.Ok index) after afterBudget)
    (law : Platform.AllocCorrect ops) :
    ∃ function, InitializerCode function expr ty ∧ index.val = before.functions.val.length ∧
      after = {before with functions := after.functions} ∧
      after.functions.val = before.functions.val ++ [function] := by
  cases effect with
  | published stages checked pushed =>
    exact ⟨stages.result, stages.certified law, rfl, rfl, (budget_push_success ops law _ _ _ _ _ pushed).2⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.expression.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (fits : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]
    scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]
    scalar_tac
  obtain ⟨⟨status, constantBudget, function⟩, constantCalled, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget (initializerSeed ty) expr ty 0#u32 codeFits poolFits)
  rw [constantCalled, bind_ok]
  simp only [uncurry_apply_pair]
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok unitValue =>
    cases unitValue
    have lowered := (runtime.compiler.initialize.constant.inv ops budget constantBudget
      (initializerSeed ty) function expr ty 0#u32 (.Ok ()) constantCalled).success law
    obtain ⟨code, pool, instruction, frame, appended, certified⟩ := lowered
    have returnFits : function.code.val.length < Usize.max := by
      rw [frame]
      change code.val.length < Usize.max
      rw [appended]
      simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append, List.length_singleton]
      scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with runtime.compiler.initialize.emit.total ops law constantBudget function.code _ returnFits
      as ⟨status, returnBudget, finalCode⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with well_formed_total {function with code := finalCode} as ⟨valid⟩
      cases valid with
      | false => simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
      | true =>
        simp only [ite_true]
        step with budget_push ops law returnBudget module.functions {function with code := finalCode} fits
          as ⟨status, afterBudget, functions, changed⟩
        cases status <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]

@[step] theorem _root_.Itasca.runtime.compiler.initialize.expression.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (functionsRequest : module.functions.length + 1 ≤ bound)
    (functionsFit : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ (status, after, afterBudget) =>
      status = .Ok (alloc.vec.Vec.len module.functions) ∧
      afterBudget.instructions.val = budget.instructions.val + 2 ∧ afterBudget.limits = budget.limits ∧
      ∃ function, InitializerCode function expr ty ∧ after.functions.val = module.functions.val ++ [function] ∧
        after = {module with functions := after.functions} ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil]
    scalar_tac
  have firstRequest : (initializerSeed ty).code.length + 1 ≤ bound := by
    simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil, Nat.zero_add]
      using (show 1 ≤ bound by omega)
  have poolReady : ∀ lo hi, expr = .V128 lo hi →
      (initializerSeed ty).v128_pool.length < Usize.max ∧
      (initializerSeed ty).v128_pool.length ≤ U32.max ∧
      (initializerSeed ty).v128_pool.length + 1 ≤ bound := by
    intros lo hi matching
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil, Nat.zero_add]
    constructor
    · scalar_tac
    exact ⟨by scalar_tac, by omega⟩
  step with runtime.compiler.initialize.constant.available ops bound available budget (initializerSeed ty) expr ty 0#u32
    (by omega) codeFits firstRequest poolReady
    as ⟨status, charged, function, accepted, usedInstructions, chargedFrame, used, lowered⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have usedCount : charged.instructions.val = budget.instructions.val + 1 := by rw [chargedFrame]; exact used
  have limits : charged.limits = budget.limits := by rw [chargedFrame]
  obtain ⟨code, pool, instruction, same, emitted, constant⟩ := lowered
  have firstCode : function.code.val = [instruction] := by
    rw [same]
    simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using emitted
  have firstLength : function.code.length = 1 := by
    simp only [alloc.vec.Vec.length, firstCode, List.length_singleton]
  step with runtime.compiler.initialize.emit.available ops bound available charged function.code
    (.Return 0#u32 (initializerWidth ty)) (by rw [limits]; omega)
    (by rw [firstLength]; scalar_tac) (by omega)
    as ⟨status, chargedAgain, finalCode, accepted, usedAgain, returnFrame, returnCount, returned⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have shape : InitializerCode {function with code := finalCode} expr ty := by
    refine ⟨⟨instruction, constant.change_code rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [returned, firstCode, List.cons_append, List.nil_append]
    all_goals simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]
  have checked := initializer_well_formed {function with code := finalCode} expr ty shape
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val])
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val])
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) vector
  step with checked as ⟨valid, validEq⟩
  rw [validEq]
  simp only [ite_true]
  step with budget_push_available ops bound available chargedAgain module.functions
    {function with code := finalCode} functionsFit functionsRequest
    as ⟨status, afterBudget, functions, accepted, sameBudget, appended⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
  refine ⟨rfl, ?_, ?_, _, shape, appended, rfl⟩
  · rw [sameBudget, returnFrame]
    change usedAgain.val = budget.instructions.val + 2
    omega
  · rw [sameBudget, returnFrame, limits]

end Itasca.Compiler

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Expression compilation is total with one available retained-function slot.
The bytecode checker is total even when it rejects the synthetic function. -/
@[step] theorem initializer_expression_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.expression ops m budget expr ty ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ⦄ := by
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.expression.total ops law m budget expr ty functionsFit)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.expression.inv ops m after budget afterBudget expr ty status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

end Itasca.Compiler

end

end

/-! ## ElementLoopContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects ElementValueContracts, ElementLoopContracts.
Each section documents its contracts and consumers.
-/

/-! ## ElementValueContracts -/

section

/-!
# Element initializer values

Expression compilation and temporary mapping append are separate stages. The effect records their normal error states and the frame/growth properties used by element traversal.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

private theorem initializer_element_type_eq (element : Itasca.wasm_types.ElemType) :
    Itasca.wasm_types.ElemType.value_type element = .ok (Itasca.Module.Constants.referenceValueType element) := by
  cases element <;> rfl

/-- Element values compile an expression and append its index to the temporary
mapping vector, keeping both stages' normal error states. -/
inductive InitializerElementValueEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule →
    runtime.compiler.Budget A → alloc.vec.Vec Usize → Prop where
  | rejected {error middle afterBudget}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget expr ty =
        .ok (.Err error, middle, afterBudget)) :
      InitializerElementValueEffect ops before budget indices expr ty (.Err error) middle afterBudget indices
  | appended {functionIndex middle expressionBudget status afterBudget outIndices}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget expr ty =
        .ok (.Ok functionIndex, middle, expressionBudget))
      (pushed : runtime.compiler.Budget.push ops expressionBudget indices functionIndex =
        .ok (status, afterBudget, outIndices)) :
      InitializerElementValueEffect ops before budget indices expr ty status middle afterBudget outIndices

theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize) (i j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_value ops before budget indices i j =
      .ok (status, after, afterBudget, outIndices)) :
    ∃ segment expr, Slice.index_usize before.module.env.elements.deref i = .ok segment ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ConstExpr) segment.init j = .ok expr ∧
      InitializerElementValueEffect ops before budget indices expr (Itasca.Module.Constants.referenceValueType segment.elem)
        status after afterBudget outIndices := by
  unfold runtime.compiler.initialize.lower_element_value at called
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Env.impl.elements, bind_ok] at called
  obtain ⟨segment, selected, tail⟩ := bind_ok_inv _ _ _ called
  obtain ⟨expr, valueSelected, tail⟩ := bind_ok_inv _ _ _ tail
  refine ⟨segment, expr, selected, valueSelected, ?_⟩
  rw [selected, bind_ok, initializer_element_type_eq, bind_ok] at tail
  obtain ⟨⟨expressionStatus, middle, expressionBudget⟩, expressionCalled, tail⟩ := bind_ok_inv _ _ _ tail
  cases expressionStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl, rfl⟩ := tail
    exact .rejected expressionCalled
  | Ok functionIndex =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨pushedStatus, pushedBudget, pushedIndices⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl, rfl⟩ := tail
    exact .appended expressionCalled pushed

theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.inv_selected {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_value ops before budget indices i j =
      .ok (status, after, afterBudget, outIndices)) :
    InitializerElementValueEffect ops before budget indices expr (Itasca.Module.Constants.referenceValueType segment.elem)
      status after afterBudget outIndices := by
  obtain ⟨actual, value, selected, valueSelected, effect⟩ :=
    runtime.compiler.initialize.lower_element_value.inv ops before after budget afterBudget indices outIndices i j status called
  rw [initializer_slice_index before.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)] at selected
  have same := Result.ok_injective selected
  subst actual
  rw [initializer_vec_index _ _ expr valueFound] at valueSelected
  have valueEq := Result.ok_injective valueSelected
  subst value
  exact effect

theorem InitializerElementValueEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty status}
    (effect : InitializerElementValueEffect ops before budget indices expr ty status after afterBudget outIndices) :
    after = {before with functions := after.functions} := by
  cases effect with
  | rejected expressionCalled => exact (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
  | appended expressionCalled pushed => exact (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame

theorem InitializerElementValueEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty status}
    (effect : InitializerElementValueEffect ops before budget indices expr ty status after afterBudget outIndices)
    (law : Platform.AllocCorrect ops) :
    after.functions.val.length ≤ before.functions.val.length + 1 ∧ outIndices.val.length ≤ indices.val.length + 1 := by
  cases effect with
  | rejected expressionCalled =>
    exact ⟨(runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).growth law, by omega⟩
  | appended expressionCalled pushed =>
    refine ⟨(runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).growth law, ?_⟩
    have changed := budget_push_code_result ops law _ _ _ _ _ _ pushed
    rcases changed with same | appended
    · rw [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem InitializerElementValueEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty}
    (effect : InitializerElementValueEffect ops before budget indices expr ty (.Ok ()) after afterBudget outIndices)
    (law : Platform.AllocCorrect ops) :
    ∃ function functionIndex, InitializerCode function expr ty ∧ functionIndex.val = before.functions.val.length ∧
      after = {before with functions := after.functions} ∧ after.functions.val = before.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [functionIndex] := by
  cases effect with
  | appended expressionCalled pushed =>
    obtain ⟨function, certified, indexEq, frame, appended⟩ :=
      (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).success law
    exact ⟨function, _, certified, indexEq, frame, appended, (budget_push_success ops law _ _ _ _ _ pushed).2⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (functionsFit : module.functions.length < Usize.max) (indicesFit : indices.length < Usize.max) :
    runtime.compiler.initialize.lower_element_value ops module budget indices i j ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Env.impl.elements, bind_ok]
  have selected := initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)
  have valueSelected := initializer_vec_index _ _ expr valueFound
  simp only [selected, valueSelected, bind_ok, initializer_element_type_eq]
  step with runtime.compiler.initialize.expression.total ops law module budget expr _ functionsFit
    as ⟨status, middle, expressionBudget⟩
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok functionIndex =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law expressionBudget indices functionIndex indicesFit
      as ⟨status, afterBudget, outIndices, changed⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (vector : ∀ lo hi, expr = .V128 lo hi → Itasca.Module.Constants.referenceValueType segment.elem = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (functionsRequest : module.functions.length + 1 ≤ bound) (functionsFit : module.functions.length < Usize.max)
    (indicesRequest : indices.length + 1 ≤ bound) (indicesFit : indices.length < Usize.max) :
    runtime.compiler.initialize.lower_element_value ops module budget indices i j ⦃ (status, after, afterBudget, outIndices) =>
      status = .Ok () ∧ afterBudget.instructions.val = budget.instructions.val + 2 ∧
      afterBudget.limits = budget.limits ∧ after = {module with functions := after.functions} ∧
      outIndices.val = indices.val ++ [alloc.vec.Vec.len module.functions] ∧
      ∃ function, InitializerCode function expr (Itasca.Module.Constants.referenceValueType segment.elem) ∧
        after.functions.val = module.functions.val ++ [function] ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Env.impl.elements, bind_ok]
  have selected := initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)
  have valueSelected := initializer_vec_index _ _ expr valueFound
  simp only [selected, valueSelected, bind_ok, initializer_element_type_eq]
  step with runtime.compiler.initialize.expression.available ops bound available module budget expr _
    vector instructions codeRequest functionsRequest functionsFit
    as ⟨status, middle, expressionBudget, accepted, count, limits, function, certified, appended, frame⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available expressionBudget indices
    (alloc.vec.Vec.len module.functions) indicesFit indicesRequest
    as ⟨status, afterBudget, outIndices, accepted, budgetEq, pushed⟩
  refine ⟨accepted, ?_, ?_, frame, pushed, function, certified, appended⟩
  · rw [budgetEq]
    exact count
  · rw [budgetEq]
    exact limits

end Itasca.Compiler

end

/-! ## ElementLoopContracts -/

section

open Itasca.Representation

/-!
# Element-value traversal

The loop contract describes actual calls and invariants for compiling each element initializer value. Element-segment lowering consumes the accumulated mapping.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

private abbrev ElementInitializerState (A : Type) := runtime.compiler.ExecutableModule ×
  runtime.compiler.Budget A × alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError

private theorem element_loop_body_eq {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (segment : Itasca.metadata.Element) (found : module.module.env.elements.val[i.val]? = some segment) :
    runtime.compiler.initialize.lower_element_loop.body ops i module budget indices j status =
      if j < alloc.vec.Vec.len segment.init then
        match status with
        | .Err _ => .ok (.done (module, budget, indices, status))
        | .Ok () => do
          let (result, next, nextBudget, nextIndices) ← runtime.compiler.initialize.lower_element_value ops module budget indices i j
          let nextIndex ← j + 1#usize
          Result.ok (.cont (next, nextBudget, nextIndices, nextIndex, result))
      else .ok (.done (module, budget, indices, status)) := by
  unfold runtime.compiler.initialize.lower_element_loop.body
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found), bind_ok]
  cases status with
  | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.is_ok, bind_ok, ite_true]

/-- Source invocation and invariant callbacks for one element-value traversal. -/
structure ElementLoopInvariant (A : Type) where
  ops : runtime.platform.Alloc A
  before : runtime.compiler.ExecutableModule
  budget : runtime.compiler.Budget A
  indices : alloc.vec.Vec Usize
  i : Usize
  j : Usize
  status : core.result.Result Unit Itasca.error.VisitError
  segment : Itasca.metadata.Element
  found : before.module.env.elements.val[i.val]? = some segment
  bounded : j.val ≤ segment.init.val.length
  P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize),
      current.module = before.module → cursor.val < segment.init.val.length → P current charged scratch cursor (.Ok ()) →
      ∀ result next nextBudget nextIndices (nextIndex : Usize),
        runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor =
          .ok (result, next, nextBudget, nextIndices) → nextIndex.val = cursor.val + 1 →
        P next nextBudget nextIndices nextIndex result
  finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → cursor.val ≤ segment.init.val.length → P current charged scratch cursor result →
      (cursor.val = segment.init.val.length ∨ result ≠ .Ok ()) → Q current charged scratch result
  initial : P before budget indices j status

/-- All normal loop returns transport the supplied invariant. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.inv {A : Type}
    (context : ElementLoopInvariant A)
    (after : runtime.compiler.ExecutableModule) (afterBudget : runtime.compiler.Budget A)
    (outIndices : alloc.vec.Vec Usize) (result : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_loop context.ops context.before context.budget
      context.i context.indices context.j context.status = .ok (after, afterBudget, outIndices, result)) :
    context.Q after afterBudget outIndices result := by
  rcases context with ⟨ops, before, budget, indices, i, j, status, segment, found, bounded,
    P, Q, advance, finish, initial⟩
  let measure : ElementInitializerState A → Nat := fun (_, _, _, cursor, _) =>
    segment.init.val.length - cursor.val
  let invariant : ElementInitializerState A → Prop := fun (current, charged, scratch, cursor, result) =>
    current.module = before.module ∧ cursor.val ≤ segment.init.val.length ∧ P current charged scratch cursor result
  unfold runtime.compiler.initialize.lower_element_loop at called
  apply initializer_loop_success _ measure invariant
    (fun (current, charged, scratch, result) => Q current charged scratch result) ?_ _ ⟨rfl, bounded, initial⟩ _ called
  rintro ⟨current, charged, scratch, cursor, result⟩ ⟨source, position, prior⟩ flow body
  have selected : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
  simp only [uncurry_apply_pair, element_loop_body_eq ops current charged scratch i cursor result segment selected] at body
  by_cases more : cursor < alloc.vec.Vec.len segment.init
  · rw [if_pos more] at body
    have inside : cursor.val < segment.init.val.length := by scalar_tac
    cases result with
    | Err error =>
      have output := Result.ok_injective body
      subst flow
      exact finish current charged scratch cursor (.Err error) source position prior (.inr (by intro impossible; cases impossible))
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨nextResult, next, nextBudget, nextIndices⟩, lowered, tail⟩ := bind_ok_inv _ _ _ body
      obtain ⟨nextIndex, added, tail⟩ := bind_ok_inv _ _ _ tail
      have output := Result.ok_injective tail
      subst flow
      have increment : cursor + 1#usize ⦃ next => next.val = cursor.val + 1 ⦄ := by
        have size := segment.init.property
        step as ⟨next, nextEq⟩
        scalar_tac
      rw [added] at increment
      simp only [WP.spec_ok] at increment
      obtain ⟨actualSegment, expr, read, valueRead, effect⟩ :=
        runtime.compiler.initialize.lower_element_value.inv ops current next charged nextBudget scratch nextIndices i cursor nextResult lowered
      have nextSource := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
      refine ⟨⟨nextSource.trans source, ?_, advance current charged scratch cursor source inside prior
        nextResult next nextBudget nextIndices nextIndex lowered increment⟩, ?_⟩
      · omega
      · dsimp only [measure]
        omega
  · rw [if_neg more] at body
    have output := Result.ok_injective body
    subst flow
    have last : cursor.val = segment.init.val.length := by
      have notInside : ¬ cursor.val < segment.init.val.length := by scalar_tac
      omega
    exact finish current charged scratch cursor result source position prior (.inl last)

/-- Normal loop execution follows any normally returning callback contract.
The callback postcondition may express exact mappings or resource bounds. -/
@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.total {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment) (bounded : j.val ≤ segment.init.val.length)
    (P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop)
    (Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop)
    (advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize),
      current.module = before.module → cursor.val < segment.init.val.length → P current charged scratch cursor (.Ok ()) →
      runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor
        ⦃ (result, next, nextBudget, nextIndices) => ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndices nextIndex result ⦄)
    (finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → cursor.val ≤ segment.init.val.length → P current charged scratch cursor result →
      (cursor.val = segment.init.val.length ∨ result ≠ .Ok ()) → Q current charged scratch result)
    (initial : P before budget indices j status) :
    runtime.compiler.initialize.lower_element_loop ops before budget i indices j status
      ⦃ (after, afterBudget, outIndices, result) => Q after afterBudget outIndices result ⦄ := by
  let measure : ElementInitializerState A → Nat := fun (_, _, _, cursor, _) =>
    segment.init.val.length - cursor.val
  let invariant : ElementInitializerState A → Prop := fun (current, charged, scratch, cursor, result) =>
    current.module = before.module ∧ cursor.val ≤ segment.init.val.length ∧ P current charged scratch cursor result
  unfold runtime.compiler.initialize.lower_element_loop
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨current, charged, scratch, cursor, result⟩ ⟨source, position, prior⟩
    have selected : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
    simp only [uncurry_apply_pair, element_loop_body_eq ops current charged scratch i cursor result segment selected]
    by_cases more : cursor < alloc.vec.Vec.len segment.init
    · rw [if_pos more]
      have inside : cursor.val < segment.init.val.length := by scalar_tac
      cases result with
      | Err error =>
        exact WP.spec.ret (finish current charged scratch cursor (.Err error) source position prior
          (.inr (by intro impossible; cases impossible)))
      | Ok unitValue =>
        cases unitValue
        obtain ⟨⟨nextResult, next, nextBudget, nextIndices⟩, lowered, post⟩ := WP.spec_imp_exists
          (advance current charged scratch cursor source inside prior)
        simp only [lowered, bind_ok, uncurry_apply_pair]
        obtain ⟨actualSegment, expr, read, valueRead, effect⟩ :=
          runtime.compiler.initialize.lower_element_value.inv ops current next charged nextBudget scratch nextIndices i cursor nextResult lowered
        have nextSource := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
        have size := segment.init.property
        step as ⟨nextIndex, increment⟩
        refine ⟨⟨nextSource.trans source, ?_, post nextIndex (by scalar_tac)⟩, ?_⟩
        · scalar_tac
        · dsimp only [measure]
          scalar_tac
    · rw [if_neg more]
      have last : cursor.val = segment.init.val.length := by
        have notInside : ¬ cursor.val < segment.init.val.length := by scalar_tac
        omega
      exact WP.spec.ret (finish current charged scratch cursor result source position prior (.inl last))
  · exact ⟨rfl, bounded, initial⟩

/-- A successful callback at every remaining source index yields a successful
loop. The caller supplies its exact invariant and final postcondition. -/
@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.available {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment) (bounded : j.val ≤ segment.init.val.length)
    (P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize → Prop)
    (Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Prop)
    (advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize), current.module = before.module →
      cursor.val < segment.init.val.length → P current charged scratch cursor →
      runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor
        ⦃ (result, next, nextBudget, nextIndices) => result = .Ok () ∧ ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndices nextIndex ⦄)
    (finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize), current.module = before.module →
      cursor.val = segment.init.val.length → P current charged scratch cursor → Q current charged scratch)
    (initial : P before budget indices j) :
    runtime.compiler.initialize.lower_element_loop ops before budget i indices j (.Ok ())
      ⦃ (after, afterBudget, outIndices, result) => result = .Ok () ∧ Q after afterBudget outIndices ⦄ := by
  apply runtime.compiler.initialize.lower_element_loop.total ops before budget indices i j (.Ok ()) segment found bounded
    (fun current charged scratch cursor result => result = .Ok () ∧ P current charged scratch cursor)
    (fun current charged scratch result => result = .Ok () ∧ Q current charged scratch)
  · intro current charged scratch cursor source inside prior
    apply WP.spec_mono (advance current charged scratch cursor source inside prior.2)
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨accepted, post⟩ nextIndex increment
    exact ⟨accepted, post nextIndex increment⟩
  · intro current charged scratch cursor result source position prior stopped
    refine ⟨prior.1, ?_⟩
    have last := stopped.resolve_right (by intro rejected; exact rejected prior.1)
    exact finish current charged scratch cursor source last prior.2
  · exact ⟨rfl, initial⟩

@[step] theorem initializer_element_value_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val < segment.init.val.length) (capacity : indices.val.length < Usize.max)
    (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_value ops m budget indices i j ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ∧
      out.2.2.2.val.length ≤ indices.val.length + 1 ⦄ := by
  let expr := segment.init.val[j.val]'bound
  have valueFound : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget, outIndices⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.lower_element_value.total ops law m budget indices i j segment expr found valueFound functionsFit capacity)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.lower_element_value.inv_selected ops m after budget afterBudget indices outIndices
    i j segment expr found valueFound status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_, growth.2⟩
  rw [frame]
  simp only [initializerSize]
  omega

/-- Element values accept from independent initializer typing, with separate
bounds for retained functions and the temporary initializer-index vector. -/
theorem initializer_element_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val < segment.init.val.length)
    (typed : Itasca.Module.Constants.Valid module.module.env segment.init.val[valueIndex.val]
      (Itasca.Module.Constants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 1 ≤ bound)
    (capacity : initializerSize module + 1 ≤ Usize.max)
    (indexCapacity : indices.length < Usize.max) (indexRequest : indices.length + 1 ≤ bound) :
    runtime.compiler.initialize.lower_element_value ops module budget indices index valueIndex ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.1.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 1 ∧ out.2.2.2.length = indices.length + 1 ⦄ := by
  let expr := segment.init.val[valueIndex.val]'inside
  have valueFound : segment.init.val[valueIndex.val]? = some expr := List.getElem?_eq_getElem inside
  have valid : Itasca.Module.Constants.Valid module.module.env expr
      (Itasca.Module.Constants.referenceValueType segment.elem) := typed
  have vector : ∀ lo hi, expr = .V128 lo hi → Itasca.Module.Constants.referenceValueType segment.elem = .V128 := by
    intros lo hi matching
    rw [matching] at valid
    generalize valueTypeEq : Itasca.Module.Constants.referenceValueType segment.elem = valueType at valid ⊢
    cases valid
    rfl
  apply WP.spec_mono (runtime.compiler.initialize.lower_element_value.available ops bound available module budget indices index valueIndex
    segment expr lookup valueFound vector instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    indexRequest indexCapacity)
  rintro ⟨status, after, afterBudget, outIndices⟩ ⟨accepted, count, limits, frame, mapped, function, certified, appended⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_, ?_⟩
  · rw [frame]
    simp only [initializerSize, appended, List.length_append, List.length_singleton]
    omega
  · simp only [alloc.vec.Vec.length, mapped, List.length_append, List.length_singleton]

@[step] theorem initializer_element_values_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (indices : alloc.vec.Vec Usize) (j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val ≤ segment.init.val.length) (indicesBound : indices.val.length ≤ j.val)
    (space : initializerSize m + (segment.init.val.length - j.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_loop ops m budget i indices j status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + (segment.init.val.length - j.val) ⦄ := by
  let P := fun (current : runtime.compiler.ExecutableModule) (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize)
      (_ : core.result.Result Unit Itasca.error.VisitError) =>
    initializerSize current + (segment.init.val.length - cursor.val) ≤ initializerSize m + (segment.init.val.length - j.val) ∧
    scratch.val.length ≤ cursor.val
  let Q := fun (current : runtime.compiler.ExecutableModule) (_ : runtime.compiler.Budget A) (_ : alloc.vec.Vec Usize)
      (_ : core.result.Result Unit Itasca.error.VisitError) =>
    current.module = m.module ∧ initializerSize current ≤ initializerSize m + (segment.init.val.length - j.val)
  refine WP.spec_mono (runtime.compiler.initialize.lower_element_loop.total ops m budget indices i j status segment
    found bound P Q ?_ ?_ ⟨Nat.le_refl _, indicesBound⟩) ?_
  · intro current charged scratch cursor source inside prior
    obtain ⟨size, scratchBound⟩ := prior
    have currentFound : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
    have lengthBound := segment.init.property
    apply WP.spec_mono (initializer_element_value_total ops law current charged scratch i cursor segment
      currentFound inside (by omega) (by omega))
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨nextSource, growth, indexGrowth⟩ nextIndex increment
    dsimp only at growth indexGrowth
    exact ⟨by omega, by omega⟩
  · intro current charged scratch cursor result source position prior stopped
    exact ⟨source, by have size := prior.1; omega⟩
  · rintro ⟨after, afterBudget, outIndices, result⟩ post
    exact post

/-- The complete remaining element-value loop accepts from independent source
typing and separate retained/scratch demand bounds. -/
theorem initializer_element_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val ≤ segment.init.val.length)
    (typed : ∀ expr ∈ segment.init.val, Itasca.Module.Constants.Valid module.module.env expr
      (Itasca.Module.Constants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ bound)
    (capacity : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexCapacity : indices.length + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexRequest : indices.length + (segment.init.val.length-valueIndex.val) ≤ bound) :
    runtime.compiler.initialize.lower_element_loop ops module budget index indices valueIndex (.Ok ()) ⦃ out =>
      out.2.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 = initializerSize module + (segment.init.val.length-valueIndex.val) ∧
      out.2.2.1.length = indices.length + (segment.init.val.length-valueIndex.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ⦄ := by
  let P := fun (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + (segment.init.val.length - cursor.val) = initializerSize module + (segment.init.val.length - valueIndex.val) ∧
    scratch.length + (segment.init.val.length - cursor.val) = indices.length + (segment.init.val.length - valueIndex.val) ∧
    charged.instructions.val + 2 * (segment.init.val.length - cursor.val) =
      budget.instructions.val + 2 * (segment.init.val.length - valueIndex.val)
  let Q := fun (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) =>
    current.module = module.module ∧ charged.limits = budget.limits ∧
    initializerSize current = initializerSize module + (segment.init.val.length - valueIndex.val) ∧
    scratch.length = indices.length + (segment.init.val.length - valueIndex.val) ∧
    charged.instructions.val = budget.instructions.val + 2 * (segment.init.val.length - valueIndex.val)
  refine WP.spec_mono (runtime.compiler.initialize.lower_element_loop.available ops module budget indices index valueIndex segment
    lookup inside P Q ?_ ?_ ⟨rfl, rfl, rfl, rfl⟩) ?_
  · intro current charged scratch cursor source inside prior
    obtain ⟨limits, size, scratchSize, used⟩ := prior
    have currentLookup : current.module.env.elements.val[index.val]? = some segment := by simpa only [source] using lookup
    apply WP.spec_mono (initializer_element_value_available ops bound available current charged scratch index cursor segment
      currentLookup inside (by simpa only [source] using typed _ (List.getElem_mem inside))
      (by rw [limits]; omega) codeRequest (by omega) (by omega) (by omega) (by omega))
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain, indicesAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain indicesAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega, by omega⟩
  · intro current charged scratch cursor source last prior
    obtain ⟨limits, size, scratchSize, used⟩ := prior
    exact ⟨source, limits, by omega, by omega, by omega⟩
  · rintro ⟨after, afterBudget, outIndices, result⟩ post
    exact post

end Itasca.Compiler

end

end
