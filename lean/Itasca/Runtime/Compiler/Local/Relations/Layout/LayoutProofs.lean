import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsCompiler
import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Platform.Laws
import Itasca.Support.Result

/-!
Compiler value widths, observed operand layouts, and resource-budget charging.

Main declarations include `compiler_width`, `observe_value`, and the standalone charge contracts. A direct consumer is `Compiler.Local.Relations.Function.CoreFunction`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact constructor equation for the stack-width query. -/
theorem _root_.Itasca.runtime.compiler.stack_width.eq (ty : Itasca.code.StackType) :
    runtime.compiler.stack_width ty =
      match ty with
      | .Val valueType => runtime.value.width valueType
      | .Bot => .ok 1#u32 := rfl

/-- Budget rejection records the requested resource and returns out of memory. -/
theorem _root_.Itasca.runtime.compiler.Budget.reject.eq {A : Type}
    (ops : runtime.platform.Alloc A) (budget : runtime.compiler.Budget A)
    (resource : runtime.compiler.CompileResource) :
    runtime.compiler.Budget.reject ops budget resource =
      .ok (.OutOfMemory, { budget with error := some resource }) := by
  rfl

inductive ChargeCounter where
  | instructions | branches | controls | locals
  deriving DecidableEq

abbrev ChargeCounter.resource : ChargeCounter → runtime.compiler.CompileResource
  | .instructions => .Instructions | .branches => .BranchTableEntries | .controls => .Controls | .locals => .Locals

abbrev ChargeCounter.used {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) : Usize :=
  match kind with
  | .instructions => budget.instructions | .branches => budget.branches | .controls => budget.controls | .locals => budget.locals

abbrev ChargeCounter.limit {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) : Usize :=
  match kind with
  | .instructions => budget.limits.max_instructions | .branches => budget.limits.max_branch_table_entries
  | .controls => budget.limits.max_controls | .locals => budget.limits.max_locals

abbrev ChargeCounter.replace {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) (used : Usize) : runtime.compiler.Budget A :=
  match kind with
  | .instructions => {budget with instructions := used} | .branches => {budget with branches := used}
  | .controls => {budget with controls := used} | .locals => {budget with locals := used}

/-- Available charging changes exactly one counter. All other counters,
allocator marker, error state, and limits are retained by the actual operation. -/
theorem charge_counter_available {A : Type} (ops : runtime.platform.Alloc A)
    (kind : ChargeCounter) (budget : runtime.compiler.Budget A)
    (room : (kind.used budget).val < (kind.limit budget).val) :
    runtime.compiler.Budget.charge ops budget kind.resource ⦃ out =>
      out.1 = .Ok () ∧ ∃ used, out.2 = kind.replace budget used ∧
        used.val = (kind.used budget).val + 1 ⦄ := by
  cases kind <;>
    simp only [ChargeCounter.used,ChargeCounter.limit] at room <;>
    simp only [ChargeCounter.resource,runtime.compiler.Budget.charge]
  all_goals
    split
    · rename_i full
      scalar_tac
    · step as ⟨used,advanced⟩
      exact ⟨used,rfl,advanced⟩

/-- Standalone contracts for every resource-budget charge operation. The branch-table total helper is public so its callback adapter can consume it. -/
@[step] theorem charge_instruction {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ out =>
      out.2.limits = budget.limits ∧
      (out.1 = .Ok () → out.2.instructions.val = budget.instructions.val + 1) ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject.eq, WP.spec_ok]
  · step
    simp_all
theorem charge_instruction_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ (status, after) =>
      status = .Ok () → ∃ used, after = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp only [runtime.compiler.Budget.reject.eq, bind_ok, WP.spec_ok, uncurry_apply_pair,
      reduceCtorEq, false_implies]
  · step as ⟨used, added⟩
    intro _
    exact ⟨used, rfl, added⟩
/-- Accepted instruction charging modifies exactly the instruction counter. -/
theorem charge_instruction_available_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.instructions.val < budget.limits.max_instructions.val) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ⦄ := by
  have notFull : ¬budget.instructions ≥ budget.limits.max_instructions := by scalar_tac
  simp only [runtime.compiler.Budget.charge, if_neg notFull]
  step as ⟨used, added⟩
  exact ⟨used, rfl, added⟩
@[step] theorem charge_control {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ out => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject.eq, WP.spec_ok]
  · step
theorem charge_control_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ (status, after) =>
      status = .Ok () → ∃ used, after = {budget with controls := used} ∧
        used.val = budget.controls.val + 1 ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp only [runtime.compiler.Budget.reject.eq, bind_ok, WP.spec_ok, uncurry_apply_pair,
      reduceCtorEq, false_implies]
  · step as ⟨used, added⟩
    intro _
    exact ⟨used, rfl, added⟩
theorem charge_control_available_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.controls.val < budget.limits.max_controls.val) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after = {budget with controls := used} ∧
        used.val = budget.controls.val + 1 ⦄ := by
  have notFull : ¬budget.controls ≥ budget.limits.max_controls := by scalar_tac
  simp only [runtime.compiler.Budget.charge, if_neg notFull]
  step as ⟨used, added⟩
  exact ⟨used, rfl, added⟩
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
@[step] theorem charge_local {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Locals ⦃ out => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject.eq, WP.spec_ok]
  · step
theorem charge_branch_total {A} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .BranchTableEntries ⦃ _ => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject.eq]
  · step

@[step] theorem compiler_width (ty : Itasca.wasm_types.ValueType) :
    runtime.value.width ty ⦃ word => word.val = width (Itasca.Translate.valueType ty) ⦄ := by
  cases ty <;> simp [runtime.value.width, Itasca.Translate.valueType, width, WP.spec_ok]

@[step] theorem operand_at (before : Slice U32) (depth : Usize)
    (positive : 0 < depth.val) (fits : depth.val ≤ before.val.length) :
    runtime.compiler.operand_at before depth ⦃ result =>
      result = .Ok (before.val[before.val.length - depth.val]'(by omega)) ⦄ := by
  have nonzero : depth ≠ 0#usize := by scalar_tac
  have bounded : ¬ depth > Slice.len before := by scalar_tac
  simp only [runtime.compiler.operand_at, nonzero, bounded, if_false]
  step as ⟨index, hi⟩
  step as ⟨value, hv⟩
  congr 1
  simpa [hi] using hv

/-- An operand beyond the current stack is rejected without indexing it. -/
theorem operand_at_out_of_bounds (before : Slice U32) (depth : Usize)
    (large : Slice.len before < depth) :
    runtime.compiler.operand_at before depth = .ok (.Err Itasca.error.VisitError.OutOfMemory) := by
  simp [runtime.compiler.operand_at, large]

@[step] theorem operand_at_total (before : Slice U32) (depth : Usize) :
    runtime.compiler.operand_at before depth ⦃ out =>
      ∀ word, out = .Ok word → word ∈ before.val ⦄ := by
  by_cases zero : depth = 0#usize
  · simp [runtime.compiler.operand_at, zero, WP.spec_ok]
  · by_cases large : depth > Slice.len before
    · simp [runtime.compiler.operand_at, zero, large, WP.spec_ok]
    · have positive : 0 < depth.val := by scalar_tac
      have fits : depth.val ≤ before.val.length := by scalar_tac
      step with operand_at before depth positive fits as ⟨out, exactValue⟩
      rename_i word success
      rw [success] at exactValue
      cases exactValue
      exact List.getElem_mem _

@[step] theorem budget_push {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (values : alloc.vec.Vec T) (value : T) (fits : values.val.length < Usize.max) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      (out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value]) ∨
      (out.1 = .Err .OutOfMemory ∧ out.2.2 = values ∧
        out.2.1.error = some .Allocation) ⦄ := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq values 1#usize
  unfold runtime.compiler.Budget.push
  rw [reserve, bind_ok]
  cases answer with
  | false => simp [runtime.compiler.Budget.reject.eq, WP.spec_ok]
  | true =>
    change (do
      let after ← alloc.vec.Vec.push values value
      pure (core.result.Result.Ok (), budget, after)) ⦃ out =>
        (out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value]) ∨
        (out.1 = .Err Itasca.error.VisitError.OutOfMemory ∧ out.2.2 = values ∧
          out.2.1.error = some .Allocation) ⦄
    step as ⟨after, appended⟩
    simp [appended]



/-- A successful checked append determines the vector effect without a capacity premise. -/
theorem budget_push_success {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T)
    (success : runtime.compiler.Budget.push ops budget before value = .ok (.Ok (), afterBudget, after)) :
    afterBudget = budget ∧ after.val = before.val ++ [value] := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq before 1#usize
  unfold runtime.compiler.Budget.push at success
  rw [reserve, bind_ok] at success
  cases answer with
  | false => simp [runtime.compiler.Budget.reject.eq] at success
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at success
    split at success
    · simp only [bind_ok] at success
      have output := Result.ok_injective success
      have hb := congrArg (fun out => out.2.1) output
      have hv := congrArg (fun out => out.2.2.val) output
      exact ⟨hb.symm, by simpa using hv.symm⟩
    · simp only [bind_fail, fail_not_ok] at success

/-- A normally returning addition determines its mathematical sum, without
assuming the absence of overflow beforehand. -/
theorem control_add_success {ty : UScalarTy} {left right out : UScalar ty}
    (success : (left + right : Result (UScalar ty)) = .ok out) : out.val = left.val + right.val := by
  have spec := UScalar.add_equiv left right
  simp only [success] at spec
  exact spec.2.1

/-- Every normal checked append either keeps the vector or appends its value. -/
theorem budget_push_code_result {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.Budget.push ops budget before value = .ok (status, afterBudget, after)) :
    after.val = before.val ∨ after.val = before.val ++ [value] := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq before 1#usize
  unfold runtime.compiler.Budget.push at accepted
  rw [reserve, bind_ok] at accepted
  cases answer with
  | false =>
    simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, runtime.compiler.Budget.reject.eq,
      bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
    exact Or.inl (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at accepted
    split at accepted
    · simp only [bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
      apply Or.inr
      simpa only [alloc.vec.Vec.from_val, List.concat_eq_append] using
        (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
    · simp only [bind_fail, fail_not_ok] at accepted

/-- An available bounded reserve request makes the actual compiler append
succeed with the exact appended vector and unchanged budget. -/
theorem budget_push_available {A T : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (values : alloc.vec.Vec T) (value : T)
    (fits : values.val.length < Usize.max) (request : values.val.length + 1 ≤ bound) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄ := by
  have reserve := available T values 1#usize (by simpa using request)
  unfold runtime.compiler.Budget.push
  rw [reserve,bind_ok]
  change (do
    let after ← alloc.vec.Vec.push values value
    pure (core.result.Result.Ok (),budget,after)) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄
  step as ⟨after,appended⟩
  exact appended

@[step] theorem observe_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (before : alloc.vec.Vec U32) (height : U32) (ty : Itasca.code.StackType)
    (fits : before.val.length < Usize.max) :
    runtime.compiler.observe_value ops budget before height ty ⦃ out =>
      match out.1 with
      | .Ok _ => out.2.1 = budget ∧ out.2.2.1.val = before.val ++ [height] ∧
          out.2.2.2.val = height.val + compilerStackWidth ty
      | .Err _ => out.2.2.2 = height ⦄ := by
  unfold runtime.compiler.observe_value
  step with budget_push ops law budget before height fits as ⟨r, budget1, before1, hp⟩
  rcases hp with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
  · cases ty <;> simp only [runtime.compiler.stack_width] <;> step* <;> cases ‹Option U32› <;>
      simp_all [compilerStackWidth, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Invert an ordinary result of an extracted monadic bind. -/
theorem initializer_bind_success {T U : Type} {input : Result T} {next : T → Result U}
    {out : U} (success : (input >>= next) = .ok out) :
    ∃ value, input = .ok value ∧ next value = .ok out := by
  change Aeneas.Std.bind input next = .ok out at success
  cases input with
  | ret value => exact ⟨value, rfl, by simpa only [bind_ok] using success⟩
  | vis event continuation => simp only [bind_vis] at success; exact (vis_not_ok success).elim
  | div => simp only [bind_div] at success; exact (div_not_ok success).elim

/-- Partial correctness for actual loops with a decreasing successful body.
This theorem makes no termination claim for a failing or divergent body. -/
theorem initializer_loop_success {S O : Type} (body : S → Result (ControlFlow S O))
    (measure : S → Nat) (inv : S → Prop) (post : O → Prop)
    (sound : ∀ state, inv state → ∀ flow, body state = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out)
    (state : S) (initial : inv state) (out : O) (success : loop body state = .ok out) : post out := by
  suffices ∀ n state, measure state = n → inv state → loop body state = .ok out → post out by
    exact this (measure state) state rfl initial success
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro current hmeasure hcurrent returned
    rw [loop.eq_def] at returned
    obtain ⟨flow, step, rest⟩ := initializer_bind_success returned
    have effect := sound current hcurrent flow step
    cases flow with
    | done answer =>
      have same := Result.ok_injective rest
      subst answer
      exact effect
    | cont next =>
      exact ih (measure next) (by simpa [hmeasure] using effect.2) next rfl effect.1 rest

@[step] theorem bounded_index (value : Usize) :
    runtime.compiler.bounded_index value ⦃ result =>
      ∀ word, result = .Ok word → word.val = value.val ⦄ := by
  unfold runtime.compiler.bounded_index
  step
  split
  · simp
  · step as ⟨word, hword⟩
    intro w equality
    cases equality
    simp only [hword, UScalar.cast_val_eq]
    simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac

/-- A source-bounded auxiliary index passes the executable u32 gate. -/
theorem bounded_index_available (value : Usize) (bounded : value.val ≤ U32.max) :
    runtime.compiler.bounded_index value ⦃ out =>
      ∃ index, out = .Ok index ∧ index.val = value.val ⦄ := by
  unfold runtime.compiler.bounded_index
  step as ⟨maximum,maximumEq⟩
  have inside : ¬ value > maximum := by
    simp_all [core.num.U32.MAX,U32.rMax]
    scalar_tac
  simp only [if_neg inside]
  step as ⟨index,indexEq⟩
  refine ⟨index,rfl,?_⟩
  simp only [indexEq,UScalar.cast_val_eq]
  scalar_tac

/-- Normalize generated tuple continuations to the same projection form as the
shared publication statement. -/
theorem entry_uncurry_apply {X Y Z : Type} (next : X → Y → Z) (pair : X × Y) :
    Std.uncurry next pair = next pair.1 pair.2 := by
  cases pair
  rfl

theorem entry_uncurry_eq {X Y Z : Type} (next : X → Y → Z) :
    Std.uncurry next = fun pair => next pair.1 pair.2 := by
  funext pair
  cases pair
  rfl

theorem entry_pair_match {X Y Z : Type} (pair : X × Y) (next : X → Y → Z) :
    (match pair with | (x, y) => next x y) = next pair.1 pair.2 := by
  cases pair
  rfl

/-- Normalize Rust's try-branch continuation without copying its caller. -/
theorem entry_branch_bind {T E R : Type} (answer : core.result.Result T E)
    (next : core.ops.control_flow.ControlFlow (core.result.Result Never E) T → Result R) :
    Aeneas.Std.bind (core.result.Result.Insts.CoreOpsTry.branch answer) next =
      match answer with
      | .Ok value => next (.Continue value)
      | .Err error => next (.Break (.Err error)) := by
  cases answer <;> simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]

/-- Observation of one scalar, reference, SIMD, or polymorphic-bottom value
accepts when its independently computed slot width and reserve request fit. -/
theorem observe_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (before : alloc.vec.Vec U32)
    (height : U32) (ty : Itasca.code.StackType)
    (fits : before.length < Usize.max) (request : before.length + 1 ≤ bound)
    (slotsFit : height.val + compilerStackWidth ty ≤ U32.max) :
    runtime.compiler.observe_value ops budget before height ty ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.1.val = before.val ++ [height] ∧
      out.2.2.2.val = height.val + compilerStackWidth ty ⦄ := by
  unfold runtime.compiler.observe_value
  step with budget_push_available ops bound available budget before height fits request
    as ⟨status,charged,values,accepted,same,appended⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  cases ty with
  | Bot =>
    simp only [runtime.compiler.stack_width.eq, bind_ok]
    step as ⟨added,addSpec⟩
    cases added with
    | none => simp [compilerStackWidth] at slotsFit; scalar_tac
    | some next =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,compilerStackWidth,appended]
      scalar_tac
  | Val type =>
    simp only [runtime.compiler.stack_width.eq]
    step with compiler_width type as ⟨width,widthEq⟩
    step as ⟨added,addSpec⟩
    cases added with
    | none =>
      simp only [compilerStackWidth] at slotsFit
      scalar_tac
    | some next =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,trivial,appended,by simpa [compilerStackWidth,widthEq] using addSpec.2.1⟩

end Itasca.Runtime.Compiler
