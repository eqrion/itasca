import Exec.Code.Module.InitializerTotalBasic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem initializer_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (space : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.2.2.val.length ≤ code.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨status, nextBudget, _⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact initializer_push_total ops law nextBudget code instruction space

/-- All constant forms return normally, including an allocator or instruction
budget rejection after partial emission. Each vector grows by at most one. -/
@[step] theorem initializer_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (expr : Itasca.types.ConstExpr)
    (ty : Itasca.types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 1 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  cases expr <;> unfold runtime.compiler.initialize.constant
  all_goals repeat' first
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | omega

/-- A single segment emits at most five instructions, one vector constant,
and one table-index pair. The bounds include rejected partial emissions. -/
@[step] theorem initializer_emit_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  step
  · simpa [alloc.vec.Vec.deref] using bound
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac

@[step] theorem initializer_emit_data_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac
end Itasca.Runtime.Code
