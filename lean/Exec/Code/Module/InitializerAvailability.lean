import Exec.Code.Local.Initializer.InitializerExpressionAvailable
import Exec.Code.Module.InitializerTotalBasic
import Itasca.Module.Const.Syntax

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent constant-expression typing supplies the vector-width condition
needed by the actual initializer compiler. -/
theorem initializer_source_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType)
    (typed : Itasca.ModuleConstants.Valid module.module.env expr ty)
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
  apply initializer_expression_available ops bound available module budget expr ty _ instructions
    codeRequest functionsRequest functionsFit
  intro lo hi same
  subst expr
  cases typed
  rfl

/-- A checked global initializer publishes both its synthetic function and its
mapping under an independent combined-vector demand bound. -/
theorem initializer_global_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.ModuleConstants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env,Exec.module.Module.env,
    Itasca.module.Module.impl.env,Exec.module.Env.globals,Itasca.module.Env.impl.globals,bind_ok]
  step as ⟨global,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have valid := typed global (by rw [found]; simpa [alloc.vec.Vec.deref] using List.getElem_mem inside)
  step with initializer_source_available ops bound available module budget global.init global.gtype.valtype valid
    instructions codeRequest (by simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
    as ⟨status,middle,charged,accepted,used,limits,function,shape,appended,same⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have inits : middle.global_initializers = module.global_initializers := by rw [same]
  step with budget_push_available ops bound available charged middle.global_initializers _
    (by rw [inits]; simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
    (by rw [inits]; simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
    as ⟨status,afterBudget,initializers,accepted,sameBudget,mapped⟩
  refine ⟨accepted,?_,?_,?_,?_⟩
  · simpa [sameBudget] using used
  · simpa [sameBudget] using limits
  · change middle.module = module.module
    exact congrArg (fun value => value.module) same
  · rw [same] at mapped ⊢
    simp only [initializerSize] at *
    rw [mapped,appended]
    simp only [List.length_append,List.length_singleton]
    omega

end Exec.Code
