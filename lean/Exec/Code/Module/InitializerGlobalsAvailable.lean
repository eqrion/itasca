import Exec.Code.Module.InitializerAvailability

namespace Exec.Code
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
    simp only [runtime.compiler.ExecutableModule.env,Exec.module.Module.env,
      Itasca.module.Module.impl.env,Exec.module.Env.globals,Itasca.module.Env.impl.globals,bind_ok]
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

end Exec.Code
