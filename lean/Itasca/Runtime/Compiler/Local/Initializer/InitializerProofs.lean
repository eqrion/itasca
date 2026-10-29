import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
/-! The extracted synthetic-initializer emitter and constant compiler terminate
under allocator laws and representable vector lengths. Successful calls append
exactly the certified scalar/reference/vector instruction, with vector constants
embedded in the actual pool. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (fits : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () → out.2.2.val = code.val ++ [instruction] ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨result, charged, limits, count⟩
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (budget_push ops law charged code instruction fits)
    rintro ⟨result, b, v⟩ hp success
    rcases hp with ⟨rfl, hb, hv⟩ | ⟨rfl, hv, he⟩
    · exact hv
    · cases success

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

def ConstantLowered (before after : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (dst : U32) : Prop :=
  ∃ code pool instruction,
    after = { before with code, v128_pool := pool } ∧
    code.val = before.code.val ++ [instruction] ∧ ConstantInstruction after dst expr ty instruction

@[step] theorem initializer_constant {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () → ConstantLowered function out.2.2 expr ty dst ⦄ := by
  cases expr with
  | I32 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits, hbits⟩
    subst bits
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.i32 value ty⟩
  | I64 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits, hbits⟩
    subst bits
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.i64 value ty⟩
  | F32 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.f32 value ty⟩
  | F64 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.f64 value ty⟩
  | RefNull elem =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.refNull ty elem⟩
  | RefFunc index =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.refFunc ty index⟩
  | GlobalGet index =>
    cases ty <;> unfold runtime.compiler.initialize.constant <;> simp only [bind_ok]
    all_goals
      step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
      intro success
      refine ⟨code, function.v128_pool, _, rfl, hc success, ?_⟩
      first | exact ConstantInstruction.globalVector index | exact ConstantInstruction.global _ index (by intro h; cases h)
  | V128 lo hi =>
    unfold runtime.compiler.initialize.constant
    step with bounded_index (alloc.vec.Vec.len function.v128_pool) as ⟨result, hp⟩
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pool =>
      have poolIndex := hp pool rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨low, hlow⟩
      subst low
      step as ⟨high, hhigh⟩
      subst high
      step as ⟨shifted, hshifted, hshiftbv⟩
      step as ⟨word, hword, hwordbv⟩
      step with budget_push ops law budget function.v128_pool word poolFits as ⟨result, b, values, hv⟩
      rcases hv with ⟨hr, hb, hv⟩ | ⟨hr, hv, he⟩
      · subst result b
        simp only [bind_ok]
        step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
        intro success
        refine ⟨code, values, _, rfl, hc success, ConstantInstruction.v128 lo hi ty pool ?_⟩
        have packed : word = initializerBits lo hi := by
          apply U128.bv_eq_imp_eq
          exact hwordbv.trans (congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) hshiftbv)
        simp [hv, poolIndex, alloc.vec.Vec.len, packed]
      · subst result values
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Itasca.Runtime.Compiler
