import Itasca.Runtime.Code.Module.InitializerEmitDataAvailable

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The full source-ordered data bytecode loop accepts with five emitted
instructions per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_datas_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (sourceCount : module.module.tail.data.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ bound) :
    runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.indirect = function.indirect ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  unfold runtime.compiler.initialize.lower_loop4
  apply loop.spec_decr_nat (fun state => module.module.tail.data.val.length-state.2.1.val)
    (fun state => state.1.limits = budget.limits ∧ state.2.2.1 = .Ok () ∧
      state.2.1.val ≤ module.module.tail.data.val.length ∧
      state.1.instructions.val + 5*(module.module.tail.data.val.length-state.2.1.val) ≤
        budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      state.2.2.2.code.length + 5*(module.module.tail.data.val.length-state.2.1.val) ≤
        function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      state.2.2.2.indirect = function.indirect ∧
      state.2.2.2.v128_pool = function.v128_pool)
  · rintro ⟨charged,next,status,current⟩ ⟨limits,accepted,position,used,code,pairs,pool⟩
    dsimp only at limits accepted position used code pairs pool
    subst status
    unfold runtime.compiler.initialize.lower_loop4.body
    simp only [runtime.compiler.ExecutableModule.tail,Itasca.module.Module.impl.tail,bind_ok]
    split
    · rename_i more
      have sourceBound : next.val < module.module.tail.data.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using more
      let segment := module.module.tail.data.val[next.val]
      have lookup : module.module.tail.data.val[next.val]? = some segment := List.getElem?_eq_getElem sourceBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_emit_data_available ops bound available module charged current next segment lookup
        (typed segment (List.getElem_mem sourceBound)) (by rw [limits]; omega) (by omega) (by omega)
        (by change module.module.tail.data.val.length ≤ U32.max at sourceCount; omega)
        (sourceLengths segment (List.getElem_mem sourceBound))
        as ⟨status,afterBudget,after,accepted,usedAgain,limitsAgain,codeAgain,poolAgain,pairsAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · exact pairsAgain.trans pairs
      · exact poolAgain.trans pool
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.tail.data.val.length := by
        have ended : module.module.tail.data.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,limits,by simpa [last] using used,by simpa [last] using code,
        pairs,pool⟩
  · exact ⟨rfl,rfl,inside,Nat.le_refl _,Nat.le_refl _,rfl,rfl⟩

end Itasca.Runtime.Code
