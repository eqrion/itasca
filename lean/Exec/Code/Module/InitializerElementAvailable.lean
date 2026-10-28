import Exec.Code.Module.InitializerElementValuesAvailable
import Exec.Code.Local.Initializer.InitializerElementAppend

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- One complete element mapping is accepted from source typing and independently
bounded retained and scratch demand, including its optional active offset. -/
theorem initializer_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.module.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (typed : ∀ expr ∈ segment.init.val, Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (offsetTyped : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*segment.init.length + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + segment.init.length + 3 ≤ bound)
    (capacity : initializerSize module + segment.init.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2*segment.init.length + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + segment.init.length + 3 ⦄ := by
  have initLength : segment.init.length = segment.init.val.length := rfl
  simp only [alloc.vec.Vec.length] at instructions reserve capacity ⊢
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_available ops bound available module budget (alloc.vec.Vec.new _) index
    0#usize segment lookup (by simp) typed (by simpa [alloc.vec.Vec.length] using (show
      budget.instructions.val + 2*segment.init.length ≤ budget.limits.max_instructions.val by omega)) codeRequest
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ bound by omega))
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ bound by omega))
    as ⟨middle,charged,indices,status,accepted,same,limits,size,indexSize,used⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have sizeBound : initializerSize middle + 3 ≤ bound := by change initializerSize middle + 3 ≤ bound; omega
  have sizeCapacity : initializerSize middle + 3 ≤ Usize.max := by omega
  step with budget_push_available ops bound available charged middle.element_initializers indices
    (by simp only [initializerSize] at sizeCapacity; omega)
    (by simp only [initializerSize] at sizeBound; omega)
    as ⟨status,rowBudget,rows,accepted,sameBudget,appended⟩
  subst status rowBudget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    runtime.compiler.ExecutableModule.env,Itasca.module.Module.impl.env]
  rw [same,element_offset_found module.module.env index segment lookup,bind_ok]
  have rowSize : initializerSize {middle with module := module.module, element_initializers := rows} = initializerSize middle + 1 := by
    simp only [initializerSize,appended,List.length_append,List.length_singleton]
    omega
  generalize offsetEq : sourceElementOffset segment = offset
  cases offset with
  | none =>
    step with budget_push_available ops bound available charged middle.element_offsets none
      (by simp only [initializerSize] at sizeCapacity; omega)
      (by simp only [initializerSize] at sizeBound; omega)
      as ⟨status,afterBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_⟩
    · simpa [sameBudget,used] using (show charged.instructions.val ≤ budget.instructions.val + 2*segment.init.length+2 by omega)
    · simpa [sameBudget] using limits
    · simp only [initializerSize,appended,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at size
      omega
  | some expr =>
    have valid : Itasca.ModuleConstants.Valid module.module.env expr .I32 := by
      unfold sourceElementOffset at offsetEq
      cases mode : segment.mode with
      | Passive => simp [mode] at offsetEq
      | Declarative => simp [mode] at offsetEq
      | Active table offset =>
        simp only [mode,Option.some.injEq] at offsetEq
        subst expr
        exact offsetTyped table offset mode
    have functionBound : middle.functions.length ≤ initializerSize middle := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with initializer_source_available ops bound available {middle with module := module.module, element_initializers := rows} charged expr .I32
      (by simpa using valid) (by rw [limits]; omega) codeRequest
      (by change middle.functions.length + 1 ≤ bound; omega)
      (by change middle.functions.length < Usize.max; omega)
      as ⟨status,afterExpression,afterBudget,accepted,usedAgain,limitsAgain,function,shape,emitted,sameExpression⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have expressionSize : initializerSize afterExpression = initializerSize middle + 2 := by
      rw [sameExpression]
      simp only [initializerSize,emitted,List.length_append,List.length_singleton] at rowSize ⊢
      omega
    have offsetBound : afterExpression.element_offsets.length ≤ initializerSize afterExpression := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with budget_push_available ops bound available afterBudget afterExpression.element_offsets _
      (by change afterExpression.element_offsets.length < Usize.max; omega)
      (by change afterExpression.element_offsets.length + 1 ≤ bound; omega)
      as ⟨status,finalBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_,?_⟩
    · simpa [sameBudget] using (show afterBudget.instructions.val ≤ budget.instructions.val+2*segment.init.length+2 by omega)
    · simpa [sameBudget,limitsAgain] using limits
    · exact congrArg (fun value => value.module) sameExpression
    · simp only [initializerSize,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at expressionSize size
      omega

end Itasca.Runtime.Code
