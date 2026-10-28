import Itasca.Runtime.Code.Local.Initializer.InitializerAvailable

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Source-shaped constant initializers compile and publish successfully with
two remaining instructions and independently bounded reserve availability.
This covers every constant-expression form, including SIMD and references. -/
theorem initializer_expression_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (functionsRequest : module.functions.length + 1 ≤ bound)
    (functionsFit : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ out =>
      out.1 = .Ok (alloc.vec.Vec.len module.functions) ∧
      out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧
      ∃ function, InitializerCode function expr ty ∧
        out.2.1.functions.val = module.functions.val ++ [function] ∧
        out.2.1 = {module with functions := out.2.1.functions} ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq,bind_ok,initializer_synthetic,bind_ok]
  step with initializer_constant_available ops bound available budget (initializerSeed ty) expr ty 0#u32
    (by omega) (by simp [initializerSeed]; scalar_tac)
    (by simpa [initializerSeed] using (show 1 ≤ bound by omega))
    (by simp [initializerSeed]; scalar_tac) (by simp [initializerSeed])
    (by simpa [initializerSeed] using (show 1 ≤ bound by omega))
    as ⟨status,charged,function,accepted,used,limits,lowered⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  obtain ⟨code,pool,instruction,same,emitted,constant⟩ := lowered
  have firstCode : function.code.val = [instruction] := by simp [same,emitted,initializerSeed]
  have firstLength : function.code.length = 1 := by simp [alloc.vec.Vec.length,firstCode]
  step with initializer_emit_available ops bound available charged function.code
    (.Return 0#u32 (initializerWidth ty)) (by rw [limits]; omega)
    (by rw [firstLength]; scalar_tac) (by omega)
    as ⟨status,chargedAgain,finalCode,accepted,usedAgain,limitsAgain,returned⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have shape : InitializerCode {function with code := finalCode} expr ty := by
    refine ⟨⟨instruction,constant.change_code rfl,?_⟩,?_,?_,?_,?_⟩
    · simp [returned,firstCode]
    all_goals simp [same,initializerSeed]
  have checked := initializer_well_formed {function with code := finalCode} expr ty shape
    (by simp [same,initializerSeed]) (by simp [same,initializerSeed])
    (by simp [same,initializerSeed]) (by simp [same,initializerSeed])
    (by simp [same,initializerSeed]) vector
  step with checked as ⟨valid,validEq⟩
  rw [validEq]
  simp only [↓reduceIte]
  step with budget_push_available ops bound available chargedAgain module.functions
    {function with code := finalCode} functionsFit functionsRequest
    as ⟨status,afterBudget,functions,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  simp only [WP.spec_ok]
  exact ⟨trivial,by rw [sameBudget]; omega,by rw [sameBudget,limitsAgain,limits],
    _,shape,appended,trivial⟩

end Itasca.Runtime.Code
