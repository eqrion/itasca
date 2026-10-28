import Itasca.Runtime.Code.Local.Initializer.InitializerAcceptance

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
