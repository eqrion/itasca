import Itasca.Runtime.Compiler.Local.Initializer.InitializerProofs
/-! Successful synthetic initializer compilation retains its exact two-instruction
program, literal pool, slot width, and position in the executable module. -/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std


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
  | false => simp [runtime.compiler.Budget.reject] at success
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at success
    split at success
    · simp only [bind_ok] at success
      have output := Result.ok_injective success
      have hb := congrArg (fun out => out.2.1) output
      have hv := congrArg (fun out => out.2.2.val) output
      exact ⟨hb.symm, by simpa using hv.symm⟩
    · simp only [bind_fail, fail_not_ok] at success

def initializerSeed (ty : Itasca.types.ValueType) : runtime.bytecode.CompiledFunction :=
  { locals := alloc.vec.Vec.new _, local_slots := 0#u32, param_slots := 0#u32,
    slot_count := initializerWidth ty, max_stack := 0#usize, code := alloc.vec.Vec.new _,
    jump_tables := alloc.vec.Vec.new _, v128_pool := alloc.vec.Vec.new _,
    indirect := alloc.vec.Vec.new _, simd := alloc.vec.Vec.new _, source_offsets := alloc.vec.Vec.new _,
    controls := alloc.vec.Vec.new _, type_index := 0#u32, body_start := 0#usize, body_end := 0#usize }

theorem initializer_synthetic (ty : Itasca.types.ValueType) :
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) (initializerWidth ty) =
      .ok (initializerSeed ty) := rfl

/-- Actual successful expression lowering supplies the executable initializer certificate.
Source expression typing and runtime index resolution are separate obligations. -/
theorem initializer_expression {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType)
    (index : Usize) (after : runtime.compiler.ExecutableModule) (budgetAfter : runtime.compiler.Budget A)
    (success : runtime.compiler.initialize.expression ops module budget expr ty =
      .ok (.Ok index, after, budgetAfter)) :
    ∃ function, InitializerCode function expr ty ∧ index.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] := by
  unfold runtime.compiler.initialize.expression at success
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok] at success
  have emptyFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp [initializerSeed]
    scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp [initializerSeed]
    scalar_tac
  obtain ⟨⟨result, b1, function⟩, hconstant, hconstantPost⟩ :=
    WP.spec_imp_exists (initializer_constant ops law budget (initializerSeed ty) expr ty 0#u32 emptyFits poolFits)
  rw [hconstant, bind_ok] at success
  simp only [uncurry_apply_pair] at success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
  | Ok value =>
    cases value
    have lowered : ConstantLowered (initializerSeed ty) function expr ty 0#u32 := hconstantPost rfl
    obtain ⟨code, pool, instruction, hfunction, hcode, relation⟩ := lowered
    have codeFits : function.code.val.length < Usize.max := by
      rw [hfunction]
      change code.val.length < Usize.max
      rw [hcode]
      simp [initializerSeed]
      scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
    obtain ⟨⟨result, b2, finalCode⟩, hemit, hemitPost⟩ := WP.spec_imp_exists
      (initializer_emit ops law b1 function.code (.Return 0#u32 (initializerWidth ty)) codeFits)
    rw [hemit, bind_ok] at success
    simp only [uncurry_apply_pair] at success
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
    | Ok value =>
      cases value
      have appended := hemitPost rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
      cases checked : runtime.bytecode.CompiledFunction.well_formed { function with code := finalCode } with
      | ret valid =>
        rw [checked, bind_ok] at success
        cases valid with
        | false => simp at success
        | true =>
          simp only [↓reduceIte] at success
          cases hpush : runtime.compiler.Budget.push ops b2 module.functions
              { function with code := finalCode } with
          | ret output =>
            rcases output with ⟨result, b3, functions⟩
            rw [hpush, bind_ok] at success
            simp only [uncurry_apply_pair] at success
            cases result with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
            | Ok value =>
              cases value
              obtain ⟨hb, hfunctions⟩ := budget_push_success ops law b2 b3 module.functions functions
                { function with code := finalCode } hpush
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
              have output := Result.ok_injective success
              have hindex := congrArg Prod.fst output
              have hafter := congrArg (fun out => out.2.1) output
              have indexEq := core.result.Result.Ok.inj hindex
              change { module with functions := functions } = after at hafter
              subst after
              refine ⟨{ function with code := finalCode }, ?_, ?_, rfl, hfunctions⟩
              · refine ⟨⟨instruction, relation.change_code rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
                · rw [appended, hfunction]
                  simp [hcode, initializerSeed]
                all_goals simp [hfunction, initializerSeed]
              · simpa [alloc.vec.Vec.len] using congrArg UScalar.val indexEq.symm
          | vis effect continuation =>
            rw [hpush, bind_vis] at success
            exact (vis_not_ok success).elim
          | div =>
            rw [hpush, bind_div] at success
            exact (div_not_ok success).elim
      | vis effect continuation =>
        rw [checked, bind_vis] at success
        exact (vis_not_ok success).elim
      | div =>
        rw [checked, bind_div] at success
        exact (div_not_ok success).elim
end Itasca.Runtime.Code
