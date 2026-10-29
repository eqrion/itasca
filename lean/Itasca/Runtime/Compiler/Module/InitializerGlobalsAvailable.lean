import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Module.InitializerTotalBasic
import Itasca.Module.Const.Syntax

/-!
Availability of constant/global initializers and their global-segment fold.
-/

/-! ## Initializer Availability -/

section

namespace Itasca.Runtime.Compiler
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
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env,Itasca.module.Env.impl.globals,bind_ok]
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Globals Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed global is accepted by the actual
initializer loop. The demand is computed from the source global count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_globals_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.ModuleConstants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 = initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  unfold runtime.compiler.initialize.lower_loop0
  apply loop.spec_decr_nat (fun state => module.module.env.globals.val.length-state.2.2.1.val)
    (fun state => state.1.module = module.module ∧ state.2.1.limits = budget.limits ∧
      state.2.2.2 = .Ok () ∧ state.2.2.1.val ≤ module.module.env.globals.val.length ∧
      initializerSize state.1 + 2*(module.module.env.globals.val.length-state.2.2.1.val) =
        initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      state.2.1.instructions.val + 2*(module.module.env.globals.val.length-state.2.2.1.val) =
        budget.instructions.val + 2*(module.module.env.globals.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,limits,accepted,position,size,used⟩
    dsimp only at same limits accepted position size used
    subst status
    unfold runtime.compiler.initialize.lower_loop0.body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env,Itasca.module.Env.impl.globals,bind_ok]
    split
    · rename_i more
      have currentBound : next.val < current.module.env.globals.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using more
      have sourceBound : next.val < module.module.env.globals.val.length := by simpa [same] using currentBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_global_available ops bound available current charged next currentBound
        (by simpa [same] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega)
        as ⟨status,middle,afterBudget,accepted,usedAgain,limitsAgain,sameAgain,sizeAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact sameAgain.trans same
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.env.globals.val.length := by
        have endBound : current.module.env.globals.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using stopped
        rw [same] at endBound
        omega
      simp only [WP.spec_ok]
      exact ⟨trivial,same,by simpa [last] using size,by simpa [last] using used,limits⟩
  · exact ⟨rfl,rfl,rfl,inside,rfl,rfl⟩

end Itasca.Runtime.Compiler

end
