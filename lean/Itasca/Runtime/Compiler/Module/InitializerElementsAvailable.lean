import Itasca.Runtime.Compiler.Module.InitializerDataAvailable
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Module.InitializerTotalMappings

/-!
Availability of individual element initializers and their complete element-segment fold.
-/

/-! ## Initializer Element Value Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Element values accept from independent initializer typing, with separate
bounds for retained functions and the temporary initializer-index vector. -/
theorem initializer_element_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
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
  simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
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
  have valueType : Itasca.wasm_types.ElemType.value_type segment.elem =
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Values Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The complete remaining element-value loop accepts from independent source
typing and separate retained/scratch demand bounds. -/
theorem initializer_element_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
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
    simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- One complete element mapping is accepted from source typing and independently
bounded retained and scratch demand, including its optional active offset. -/
theorem initializer_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Element)
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
    runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env]
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Elements Available -/

section

namespace Itasca.Runtime.Compiler
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
    simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
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

end Itasca.Runtime.Compiler

end
