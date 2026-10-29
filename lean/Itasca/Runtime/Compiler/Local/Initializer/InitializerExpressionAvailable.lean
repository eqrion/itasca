import Itasca.Runtime.Compiler.Local.Initializer.InitializerAcceptance

/-!
Availability of constant initializer instructions and complete initializer expressions. The expression proof composes actual constant callback success under allocator availability.
-/

/-! ## Initializer Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- All constant-expression forms lower successfully with one remaining
instruction and independently available code/pool reserves. -/
theorem initializer_constant_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (dst : U32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (codeFits : function.code.length < Usize.max) (codeRequest : function.code.length + 1 ≤ bound)
    (poolFits : function.v128_pool.length < Usize.max)
    (poolIndex : function.v128_pool.length ≤ U32.max)
    (poolRequest : function.v128_pool.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ ConstantLowered function out.2.2 expr ty dst ⦄ := by
  cases expr with
  | I32 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits,equal⟩
    subst bits
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.i32 value ty⟩
  | I64 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits,equal⟩
    subst bits
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.i64 value ty⟩
  | F32 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.f32 value ty⟩
  | F64 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.f64 value ty⟩
  | RefNull element =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.refNull ty element⟩
  | RefFunc index =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,.refFunc ty index⟩
  | GlobalGet index =>
    cases ty <;> unfold runtime.compiler.initialize.constant <;> simp only [bind_ok]
    all_goals
      step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
        as ⟨status,after,code,accepted,used,limits,appended⟩
      refine ⟨accepted,used,limits,code,function.v128_pool,_,rfl,appended,?_⟩
      first | exact .globalVector index | exact .global _ index (by intro h; cases h)
  | V128 lo hi =>
    unfold runtime.compiler.initialize.constant runtime.compiler.bounded_index
    step as ⟨maximum,maximumEq⟩
    have bounded : ¬ alloc.vec.Vec.len function.v128_pool > maximum := by
      simp_all [core.num.U32.MAX, U32.rMax]
      scalar_tac
    simp only [if_neg bounded]
    step as ⟨pool,poolEq⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step as ⟨low,lowEq⟩
    subst low
    step as ⟨high,highEq⟩
    subst high
    step as ⟨shifted,shiftEq,shiftBits⟩
    step as ⟨word,wordEq,wordBits⟩
    step with budget_push_available ops bound available budget function.v128_pool word poolFits poolRequest
      as ⟨status,after,values,accepted,same,appended⟩
    subst status after
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available budget function.code _ room codeFits codeRequest
      as ⟨status,after,code,accepted,used,limits,emitted⟩
    refine ⟨accepted,used,limits,code,values,_,rfl,emitted,.v128 lo hi ty pool ?_⟩
    have packed : word = initializerBits lo hi := by
      apply U128.bv_eq_imp_eq
      exact wordBits.trans (congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) shiftBits)
    have poolValue : pool.val = function.v128_pool.length := by
      simp_all [UScalar.cast_val_eq]
      scalar_tac
    simp [appended,poolValue,packed]

end Itasca.Runtime.Compiler

end

/-! ## Initializer Expression Available -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
