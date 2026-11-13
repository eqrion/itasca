import Itasca.Runtime.Compiler.Module.InitializerGlobalsAvailable
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Stream.DriverRun

/-!
Sections, each formerly its own module: InitializerDataAvailable, InitializerElementsAvailable, InitializerOffsetAvailable, CompileDriverFrame.
-/

/-! ## InitializerDataAvailable -/

section

/-!
Successful data initializer compilation from independently bounded source offsets and allocator availability.
-/

/-! ## Initializer Data Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Active offsets compile from independent constant-expression typing;
passive data needs only its mapping append. Both paths accept from conservative
source-independent reserve and two-instruction headroom bounds. -/
theorem initializer_data_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_data_offset
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.metadata.Module.impl.tail,bind_ok]
  step as ⟨segment,found⟩
  have member : segment ∈ module.module.tail.data.val := by rw [found]; exact List.getElem_mem inside
  cases mode : segment.mode with
  | Active memory offset =>
    simp only [mode]
    step with initializer_source_available ops bound available module budget offset .I32
      (typed segment member memory offset mode) instructions codeRequest
      (by simp only [initializerSize,alloc.vec.Vec.length] at reserve ⊢; omega)
      (by simp only [initializerSize,alloc.vec.Vec.length] at capacity ⊢; omega)
      as ⟨status,middle,charged,accepted,used,limits,function,shape,appended,same⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have offsets : middle.data_offsets = module.data_offsets := congrArg (fun value => value.data_offsets) same
    step with budget_push_available ops bound available charged middle.data_offsets _
      (by rw [offsets]; simp only [initializerSize] at capacity; omega)
      (by rw [offsets]; simp only [initializerSize] at reserve; omega)
      as ⟨status,afterBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_,?_⟩
    · simpa [sameBudget,used]
    · simpa [sameBudget] using limits
    · change middle.module = module.module
      exact congrArg (fun value => value.module) same
    · rw [same] at mapped ⊢
      simp only [initializerSize] at *
      rw [mapped,appended]
      simp only [List.length_append,List.length_singleton]
      omega
  | Passive =>
    simp only [mode]
    step with budget_push_available ops bound available budget module.data_offsets none
      (by simp only [initializerSize] at capacity; omega)
      (by simp only [initializerSize] at reserve; omega)
      as ⟨status,afterBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_⟩
    · simp only [sameBudget]
      omega
    · simp [sameBudget]
    · simp only [initializerSize,mapped,List.length_append,List.length_singleton]
      omega

end Itasca.Runtime.Compiler

end

/-! ## Initializer Data Offsets Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed data offset is accepted by the actual
initializer loop. The demand is computed from the source data count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_data_offsets_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 ≤ initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  unfold runtime.compiler.initialize.lower_loop2
  apply loop.spec_decr_nat (fun state => module.module.tail.data.val.length-state.2.2.1.val)
    (fun state => state.1.module = module.module ∧ state.2.1.limits = budget.limits ∧
      state.2.2.2 = .Ok () ∧ state.2.2.1.val ≤ module.module.tail.data.val.length ∧
      initializerSize state.1 + 2*(module.module.tail.data.val.length-state.2.2.1.val) ≤
        initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      state.2.1.instructions.val + 2*(module.module.tail.data.val.length-state.2.2.1.val) ≤
        budget.instructions.val + 2*(module.module.tail.data.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,limits,accepted,position,size,used⟩
    dsimp only at same limits accepted position size used
    subst status
    unfold runtime.compiler.initialize.lower_loop2.body
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail,bind_ok]
    split
    · rename_i more
      have currentBound : next.val < current.module.tail.data.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using more
      have sourceBound : next.val < module.module.tail.data.val.length := by simpa [same] using currentBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_data_offset_available ops bound available current charged next currentBound
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
      have last : next.val = module.module.tail.data.val.length := by
        have endBound : current.module.tail.data.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len,alloc.vec.Vec.deref,Slice.len] using stopped
        rw [same] at endBound
        omega
      simp only [WP.spec_ok]
      exact ⟨trivial,same,by simpa [last] using size,by simpa [last] using used,limits⟩
  · exact ⟨rfl,rfl,rfl,inside,Nat.le_refl _,Nat.le_refl _⟩

end Itasca.Runtime.Compiler

end

end

/-! ## InitializerElementsAvailable -/

section

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

end

/-! ## InitializerOffsetAvailable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-typed i32 offsets compile with one instruction and no pool reserve.
The exact field effect is available before any publication checker runs. -/
theorem initializer_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (env : Itasca.metadata.Env) (expr : Itasca.wasm_types.ConstExpr)
    (typed : Itasca.ModuleConstants.Valid env expr .I32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (capacity : function.code.length < Usize.max) (request : function.code.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr .I32 0#u32 ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2 = {function with code := out.2.2.code} ∧
      ∃ instruction, out.2.2.code.val = function.code.val ++ [instruction] ∧
        ConstantInstruction out.2.2 0#u32 expr .I32 instruction ⦄ := by
  rcases valid_offset_shape typed with ⟨bits,rfl⟩ | ⟨index,rfl⟩
  · unfold runtime.compiler.initialize.constant
    step as ⟨word,wordEq⟩
    subst word
    step with initializer_emit_available ops bound available budget function.code _ room capacity request
      as ⟨status,charged,instructions,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,_,appended,.i32 bits .I32⟩
  · unfold runtime.compiler.initialize.constant
    simp only [bind_ok]
    step with initializer_emit_available ops bound available budget function.code _ room capacity request
      as ⟨status,charged,instructions,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,_,appended,.global .I32 index (by intro h; cases h)⟩

end Itasca.Runtime.Compiler

end

/-! ## CompileDriverFrame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Compiler custom-section callbacks preserve every scheduler predicate. -/
theorem compiler_custom_preserves {A : Type} (ops : runtime.platform.Alloc A)
    (P : runtime.compiler.CompileScheduler A → Prop) :
    ModuleTail.PreservesInvariant
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst P := by
  intro before chunk after accepted prior
  have same : before = after := congrArg Prod.snd (Result.ok_injective accepted)
  simpa only [← same] using prior

/-- Parsing the environment only delivers custom-section notifications, so the
actual compiler scheduler is unchanged before its environment-ready callback. -/
theorem compiler_driver_decoded {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state before after env}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env) : run.decoded = before := by
  have region : run.region = before := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_env_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) run.environment run.region env
    run.environmentLength run.decoded run.decode_environment region
  exact decoded

/-- Code-end, tail parsing/delivery and final worker retirement preserve the
function array and captured tables produced by submission. -/
theorem compiler_driver_after_submission {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.Source S} {id state env environmentLength before after}
    (run : StreamRun.Remaining source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env environmentLength before after) :
    after = {run.submitted with completed := after.completed, tail := some run.tail} := by
  have ended : run.ended = run.submitted := by
    have same := congrArg Prod.snd (Result.ok_injective run.end_call)
    exact same.symm
  have region : run.region = run.ended := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_tail_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = run.region) (compiler_custom_preserves ops _) run.tailBytes 0#usize env
    run.region run.tail run.decodedTail run.decode_tail rfl
  have ready : run.ready = {run.decodedTail with tail := some run.tail} := by
    have same := congrArg Prod.snd (Result.ok_injective run.ready_call)
    exact same.symm
  have drained := compiler_drain_frame ops id run.ready after run.pending run.remaining run.drain_call
  simpa only [ready, decoded, region, ended] using drained

/-- Actual environment preparation supplies the exact canonical signature and
parameter tables and the empty source-indexed result array. -/
theorem compiler_driver_configured {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {source : stream.Source S} {id state before after env}
    (run : StreamRun.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) :
    SignatureSequence run.remaining.configured.signatures.val env.types.val ∧
      run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      run.remaining.configured.functions.val = List.replicate env.func_type_indices.val.length none ∧
      run.remaining.configured.code_start = before.code_start := by
  have decoded := compiler_driver_decoded ops run
  have prepared := compiler_environment_ready_sequence ops law run.decoded env
    (by simpa only [decoded] using emptyTypes) (by simpa only [decoded] using emptySlots)
    (by simpa only [decoded] using emptyFunctions)
  have configured := run.remaining.configured_call
  change runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops run.decoded env =
    .ok (.Ok run.remaining.config, run.remaining.configured) at configured
  rw [configured, WP.spec_ok] at prepared
  obtain ⟨signatures, widths, functions⟩ := prepared _ rfl
  have frame := compiler_environment_frame ops run.decoded run.remaining.configured env run.remaining.config
    run.remaining.configured_call
  have origin := congrArg (fun fields => fields.2.2) frame
  exact ⟨signatures, widths, functions, by simpa only [schedulerFrame, decoded] using origin⟩
end Itasca.Runtime.Compiler

end
