import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings
import Itasca.Runtime.Compiler.Module.WellFormedTotal

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 1500000

/-- Combined retained-vector size, used only to account for append headroom. -/
def initializerSize (m : runtime.compiler.ExecutableModule) : Nat :=
  m.functions.val.length + m.global_initializers.val.length +
  m.element_initializers.val.length + m.element_offsets.val.length + m.data_offsets.val.length

@[step] theorem initializer_push_total {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (values : alloc.vec.Vec T) (value : T) (fits : values.val.length < Usize.max) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.2.2.val.length ≤ values.val.length + 1 ⦄ := by
  apply WP.spec_mono (budget_push ops law budget values value fits)
  rintro ⟨status, nextBudget, next⟩ (⟨_, _, h⟩ | ⟨_, h, _⟩)
  · simp [h]
  · change next = values at h
    simp [h]

/-- Expression compilation is total with one available retained-function slot.
The bytecode checker is total even when it rejects the synthetic function. -/
@[step] theorem initializer_expression_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.types.ConstExpr)
    (ty : Itasca.types.ValueType) (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.expression ops m budget expr ty ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp [initializerSeed]; scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp [initializerSeed]; scalar_tac
  step with initializer_constant ops law budget (initializerSeed ty) expr ty 0#u32 codeFits poolFits
    as ⟨status, budget1, function, lowered⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨code, pool, instruction, functionEq, codeEq, _⟩ := lowered rfl
    have fits : function.code.val.length < Usize.max := by
      simp [functionEq, codeEq, initializerSeed]; scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_emit ops law budget1 function.code _ fits as ⟨status, budget2, finalCode, _⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with well_formed_total { function with code := finalCode } as ⟨valid, _⟩
      cases valid with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        have capacity : m.functions.val.length < Usize.max := by unfold initializerSize at space; omega
        step with initializer_push_total ops law budget2 m.functions _ capacity as ⟨status, budget3, functions, size⟩
        cases status <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          initializerSize] <;> omega

@[step] theorem initializer_global_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.env.globals.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.globals, bind_ok]
  step as ⟨g, found⟩
  · simpa [alloc.vec.Vec.deref] using bound
  step with initializer_expression_total ops law m budget g.init g.gtype.valtype (by omega)
    as ⟨status, middle, budget1, same, size⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have capacity : middle.global_initializers.val.length < Usize.max := by
      unfold initializerSize at size space; omega
    step with initializer_push_total ops law budget1 middle.global_initializers value capacity
      as ⟨status, budget2, values, count⟩
    try simp only [WP.spec_ok]
    exact ⟨same, by unfold initializerSize at *; dsimp; omega⟩

@[step] theorem initializer_data_offset_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_data_offset
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step as ⟨segment, found⟩
  cases mode : segment.mode with
  | Active memory offset =>
    simp only [mode]
    step with initializer_expression_total ops law m budget offset .I32 (by omega)
      as ⟨status, middle, budget1, same, size⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have capacity : middle.data_offsets.val.length < Usize.max := by
        unfold initializerSize at size space; omega
      step with initializer_push_total ops law budget1 middle.data_offsets (some value) capacity
        as ⟨status, budget2, values, count⟩
      try simp only [WP.spec_ok]
      exact ⟨same, by unfold initializerSize at *; dsimp; omega⟩
  | Passive =>
    simp only [mode]
    have capacity : m.data_offsets.val.length < Usize.max := by unfold initializerSize at space; omega
    step with initializer_push_total ops law budget m.data_offsets none capacity
      as ⟨status, budget1, values, count⟩
    try simp only [WP.spec_ok]
    unfold initializerSize at *
    dsimp at *
    omega
end Itasca.Runtime.Code
