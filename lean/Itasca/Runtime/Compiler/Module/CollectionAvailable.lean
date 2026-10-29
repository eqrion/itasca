import Itasca.Runtime.Compiler.Module.CollectFunctions
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Moving a populated source slot into the dense vector succeeds when its
independently bounded append request is available. -/
theorem take_function_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (function : runtime.bytecode.CompiledFunction)
    (inside : index.val < pending.val.length) (found : pending.val[index.val]? = some (some function))
    (capacity : functions.length < Usize.max) (reserve : functions.length+1 ≤ bound) :
    runtime.compiler.take_function ops budget pending index functions ⦃ out => out.1 = .Ok () ∧ out.2.1 = budget ∧
      out.2.2.1.val = pending.val.set index.val none ∧ out.2.2.2.val = functions.val++[function] ⦄ := by
  unfold runtime.compiler.take_function
  step as ⟨value,back,lookup,restore⟩
  have element : pending.val[index.val] = some function := (List.getElem?_eq_some_iff.mp found).2
  have valueEq : value = some function := lookup.trans element
  simp only [valueEq,element,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound allocation budget functions function capacity reserve
    as ⟨reply,afterBudget,afterFunctions,status,budgetEq,appended⟩
  subst reply afterBudget
  simp only [WP.spec_ok,restore,alloc.vec.Vec.set_val_eq]
  exact ⟨True.intro,True.intro,True.intro,appended⟩

/-- Every still-pending source slot is collected successfully. This internal
loop needs only populated slots and numerical reserve room, not a final
executable or successful collection supplied by its caller. -/
theorem collect_functions_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ pending.length) (collected : functions.length = index.val)
    (reserve : pending.length ≤ bound)
    (populated : ∀ next, index.val ≤ next → next < pending.length → ∃ function, pending.val[next]? = some (some function)) :
    runtime.compiler.collect_functions_loop ops budget pending functions index (.Ok ()) ⦃ out =>
      out.2.2.2 = .Ok () ∧ out.1 = budget ⦄ := by
  unfold runtime.compiler.collect_functions_loop
  apply loop.spec_decr_nat (fun state => pending.length-state.2.2.2.1.val)
    (fun state => state.1 = budget ∧ state.2.2.2.2 = .Ok () ∧ state.2.1.length = pending.length ∧
      state.2.2.2.1.val ≤ pending.length ∧ state.2.2.1.length = state.2.2.2.1.val ∧
      ∀ next, state.2.2.2.1.val ≤ next → next < pending.length →
        ∃ function, state.2.1.val[next]? = some (some function))
  · rintro ⟨currentBudget,currentPending,currentFunctions,currentIndex,status⟩ ⟨same,accepted,length,position,output,remaining⟩
    dsimp only at same accepted length position output remaining
    subst currentBudget status
    unfold runtime.compiler.collect_functions_loop.body
    simp only [bind_ok]
    split
    · rename_i more
      have inbounds : currentIndex.val < currentPending.length := by scalar_tac
      have originalBound : currentIndex.val < pending.length := by omega
      obtain ⟨function,found⟩ := remaining currentIndex.val (Nat.le_refl _) originalBound
      have capacity : currentFunctions.length < Usize.max := by
        have wordBound := pending.property
        change pending.length ≤ Usize.max at wordBound
        omega
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with take_function_available ops bound allocation budget currentPending currentIndex currentFunctions function
        inbounds found capacity (by omega) as ⟨reply,afterBudget,afterPending,afterFunctions,success,budgetEq,pendingEq,appended⟩
      subst reply afterBudget
      step as ⟨next,increment⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.length,pendingEq,List.length_set] at length ⊢
        exact length
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton] at output ⊢
        omega
      · intro selected lower upper
        rw [pendingEq,List.getElem?_set_ne (by omega)]
        exact remaining selected (by omega) upper
      · scalar_tac
    · exact WP.spec.ret ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,inside,collected,populated⟩

/-- The actual dense collection succeeds in source order and preserves all
budget counters. Population is established by compilation's source-slot prefix. -/
theorem collect_functions_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (reserve : pending.length ≤ bound)
    (populated : ∀ index, index < pending.length → ∃ function, pending.val[index]? = some (some function)) :
    runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧
      ∃ functions, out.1 = .Ok functions ∧ pending.val = functions.val.map some ⦄ := by
  have normal : runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧ ∃ functions, out.1 = .Ok functions ⦄ := by
    unfold runtime.compiler.collect_functions
    step with collect_functions_loop_available ops bound allocation budget pending (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp [alloc.vec.Vec.new]) reserve (by intro index _ bound; exact populated index bound)
      as ⟨afterBudget,afterPending,functions,status,accepted,same⟩
    subst status afterBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨True.intro,functions,rfl⟩
  obtain ⟨⟨reply,afterBudget,afterPending⟩,called,same,functions,accepted⟩ := WP.spec_imp_exists normal
  dsimp only at same accepted
  have ordered := collect_functions_spec ops law budget pending
  rw [called,WP.spec_ok] at ordered ⊢
  exact ⟨same,functions,accepted,ordered functions accepted⟩

end Itasca.Runtime.Code
