import Itasca.Runtime.Compiler.Module.InitializerGlobalsAvailable

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
    Itasca.module.Module.impl.tail,bind_ok]
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
      Itasca.module.Module.impl.tail,bind_ok]
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
