import Itasca.Runtime.Code.Module.InitializerElementValueAvailable

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The complete remaining element-value loop accepts from independent source
typing and separate retained/scratch demand bounds. -/
theorem initializer_element_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.module.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val ≤ segment.init.val.length)
    (typed : ∀ expr ∈ segment.init.val, Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ bound)
    (capacity : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexCapacity : indices.length + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexRequest : indices.length + (segment.init.val.length-valueIndex.val) ≤ bound) :
    runtime.compiler.initialize.lower_element_loop ops module budget index indices valueIndex (.Ok ()) ⦃ out =>
      out.2.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 = initializerSize module + (segment.init.val.length-valueIndex.val) ∧
      out.2.2.1.length = indices.length + (segment.init.val.length-valueIndex.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_element_loop
  apply loop.spec_decr_nat (fun state => segment.init.val.length-state.2.2.2.1.val)
    (fun state => state.1.module = module.module ∧ state.2.1.limits = budget.limits ∧
      state.2.2.2.2 = .Ok () ∧ state.2.2.2.1.val ≤ segment.init.val.length ∧
      initializerSize state.1 + (segment.init.val.length-state.2.2.2.1.val) =
        initializerSize module + (segment.init.val.length-valueIndex.val) ∧
      state.2.2.1.length + (segment.init.val.length-state.2.2.2.1.val) =
        indices.length + (segment.init.val.length-valueIndex.val) ∧
      state.2.1.instructions.val + 2*(segment.init.val.length-state.2.2.2.1.val) =
        budget.instructions.val + 2*(segment.init.val.length-valueIndex.val))
  · rintro ⟨current,charged,scratch,next,status⟩ ⟨same,limits,accepted,position,size,scratchSize,used⟩
    dsimp only at same limits accepted position size scratchSize used
    subst status
    have currentLookup : current.module.env.elements.val[index.val]? = some segment := by simpa [same] using lookup
    have segmentBound := (List.getElem?_eq_some_iff.mp currentLookup).1
    unfold runtime.compiler.initialize.lower_element_loop.body
    simp only [runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.elements,bind_ok]
    step as ⟨selected,found⟩
    · simpa [alloc.vec.Vec.deref] using segmentBound
    have sameSegment : selected = segment := by
      simpa [alloc.vec.Vec.deref,found,List.getElem?_eq_getElem segmentBound] using currentLookup
    rw [sameSegment]
    split
    · rename_i more
      have atValue : next.val < segment.init.val.length := by scalar_tac
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_element_value_available ops bound available current charged scratch index next segment
        currentLookup atValue (by simpa [same] using typed _ (List.getElem_mem atValue))
        (by rw [limits]; omega) codeRequest (by omega) (by omega) (by omega) (by omega)
        as ⟨status,middle,afterBudget,afterIndices,accepted,usedAgain,limitsAgain,sameAgain,sizeAgain,indicesAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · exact sameAgain.trans same
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = segment.init.val.length := by scalar_tac
      exact WP.spec.ret ⟨rfl,same,limits,by simpa [last] using size,
        by simpa [last] using scratchSize,by simpa [last] using used⟩
  · exact ⟨rfl,rfl,rfl,inside,rfl,rfl,rfl⟩

end Itasca.Runtime.Code
