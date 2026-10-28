import Exec.Code.Module.InitializerElementAvailable
import Exec.Code.Module.InitializerTotalMappings

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The complete element-mapping loop accepts from source typing and a demand
computed by summing source initializer counts plus three entries per segment.
Temporary element-index vectors are bounded by this same independent demand. -/
theorem initializer_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid module.module.env expr (Itasca.ModuleConstants.referenceValueType segment.elem))
    (offsetTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ bound)
    (capacity : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 ≤ initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val +
        2*initializerElementCost (module.module.env.elements.val.drop index.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop1
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length-state.2.2.1.val)
    (fun state => state.1.module = module.module ∧ state.2.1.limits = budget.limits ∧ state.2.2.2 = .Ok () ∧
      state.2.2.1.val ≤ module.module.env.elements.val.length ∧
      initializerSize state.1 + initializerElementCost (module.module.env.elements.val.drop state.2.2.1.val) ≤
        initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
      state.2.1.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop state.2.2.1.val) ≤
        budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,limits,accepted,position,size,used⟩
    dsimp only at same limits accepted position size used
    subst status
    unfold runtime.compiler.initialize.lower_loop1.body
    simp only [runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.elements,bind_ok]
    split
    · rename_i more
      have currentBound : next.val < current.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      have sourceBound : next.val < module.module.env.elements.val.length := by simpa [same] using currentBound
      let segment := module.module.env.elements.val[next.val]
      have lookup : module.module.env.elements.val[next.val]? = some segment := List.getElem?_eq_getElem sourceBound
      have member := List.getElem_mem sourceBound
      have cost := initializer_element_cost_step _ next.val segment lookup
      have initLength : segment.init.length = segment.init.val.length := rfl
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_element_available ops bound available current charged next segment
        (by simpa [same] using lookup) (by simpa [same] using typed segment member)
        (by simpa [same] using offsetTyped segment member)
        (by rw [limits]; omega) codeRequest (by omega) (by omega)
        as ⟨status,middle,afterBudget,accepted,usedAgain,limitsAgain,sameAgain,sizeAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      have remaining : initializerElementCost (module.module.env.elements.val.drop next.val) =
          segment.init.length + 3 + initializerElementCost (module.module.env.elements.val.drop following.val) := by
        simpa [followingEq,initLength] using cost
      dsimp only [segment] at remaining
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact sameAgain.trans same
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.env.elements.val.length := by
        have ended : current.module.env.elements.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        rw [same] at ended
        omega
      exact WP.spec.ret ⟨rfl,same,limits,by simpa [last,initializerElementCost] using size,
        by simpa [last,initializerElementCost] using used⟩
  · exact ⟨rfl,rfl,rfl,inside,Nat.le_refl _,Nat.le_refl _⟩

end Itasca.Runtime.Code
