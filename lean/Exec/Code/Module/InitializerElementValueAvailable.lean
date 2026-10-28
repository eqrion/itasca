import Exec.Code.Module.InitializerDataOffsetsAvailable

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Element values accept from independent initializer typing, with separate
bounds for retained functions and the temporary initializer-index vector. -/
theorem initializer_element_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.module.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val < segment.init.val.length)
    (typed : Itasca.ModuleConstants.Valid module.module.env segment.init.val[valueIndex.val]
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 1 ≤ bound)
    (capacity : initializerSize module + 1 ≤ Usize.max)
    (indexCapacity : indices.length < Usize.max) (indexRequest : indices.length + 1 ≤ bound) :
    runtime.compiler.initialize.lower_element_value ops module budget indices index valueIndex ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.1.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 1 ∧ out.2.2.2.length = indices.length + 1 ⦄ := by
  have segmentBound := (List.getElem?_eq_some_iff.mp lookup).1
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env,Itasca.module.Env.impl.elements,bind_ok]
  step as ⟨first,found⟩
  · simpa [alloc.vec.Vec.deref] using segmentBound
  have sameFirst : first = segment := by
    simpa [alloc.vec.Vec.deref,found,List.getElem?_eq_getElem segmentBound] using lookup
  rw [sameFirst]
  step as ⟨expr,foundExpr⟩
  step as ⟨second,foundSecond⟩
  have sameSecond : second = segment := by
    simpa [alloc.vec.Vec.deref,foundSecond,List.getElem?_eq_getElem segmentBound] using lookup
  rw [sameSecond]
  have valueType : Itasca.types.ElemType.value_type segment.elem =
      .ok (Itasca.ModuleConstants.referenceValueType segment.elem) := by cases segment.elem <;> rfl
  rw [valueType,bind_ok]
  have valid : Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem) := by simpa [foundExpr] using typed
  step with initializer_source_available ops bound available module budget expr _ valid instructions codeRequest
    (by simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
    as ⟨status,middle,charged,accepted,used,limits,function,shape,appended,same⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available charged indices _ indexCapacity indexRequest
    as ⟨status,afterBudget,afterIndices,accepted,sameBudget,mapped⟩
  refine ⟨accepted,?_,?_,?_,?_,?_⟩
  · simpa [sameBudget] using used
  · simpa [sameBudget] using limits
  · exact congrArg (fun value => value.module) same
  · rw [same]
    simp only [initializerSize,appended,List.length_append,List.length_singleton]
    omega
  · simp [alloc.vec.Vec.length,mapped]

end Itasca.Runtime.Code
