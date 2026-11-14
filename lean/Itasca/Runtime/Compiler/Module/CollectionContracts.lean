import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs

/-! Ordered collection of compiled source slots into the dense executable vector. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- The pending suffix retains its source indices; the output is exactly the
already collected prefix, with no missing, duplicate, or reordered function. -/
def CollectionPrefix (original : List (Option runtime.bytecode.CompiledFunction))
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Nat) : Prop :=
  original.take index = functions.val.map some ∧ pending.val.drop index = original.drop index

theorem _root_.Itasca.runtime.compiler.take_function.total {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (bound : index.val < pending.val.length) (capacity : functions.val.length < Usize.max) :
    runtime.compiler.take_function allocator budget pending index functions ⦃ (status, afterBudget, afterPending, afterFunctions) =>
      afterPending.val.length = pending.val.length ∧
      (status = .Ok () → ∃ function,
        pending.val[index.val]? = some (some function) ∧
        afterPending.val = pending.val.set index.val none ∧
        afterFunctions.val = functions.val ++ [function]) ⦄ := by
  unfold runtime.compiler.take_function
  step as ⟨value, back, lookup, restore⟩
  cases value with
  | none =>
    simp [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      restore, alloc.vec.Vec.set_val_eq]
  | some function =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push allocator law budget functions function capacity
      as ⟨result, afterBudget, afterFunctions, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [WP.spec_ok, restore, alloc.vec.Vec.set_val_eq, List.length_set]
      refine ⟨by simp only [alloc.vec.Vec.set_val_eq, List.length_set], fun _ => ⟨function, ?_, by simp only [alloc.vec.Vec.set_val_eq], appended⟩⟩
      rw [List.getElem?_eq_getElem bound, ← lookup]
    · simp [restore, alloc.vec.Vec.set_val_eq]


theorem _root_.Itasca.runtime.compiler.collect_functions_loop.total {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (original : List (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (result : core.result.Result Unit runtime.compiler.CompileError)
    (length : pending.val.length = original.length) (bound : index.val ≤ original.length)
    (invariant : result = .Ok () → CollectionPrefix original pending functions index.val) :
    runtime.compiler.collect_functions_loop allocator budget pending functions index result ⦃ (afterBudget, afterPending, afterFunctions, status) =>
      status = .Ok () → original = afterFunctions.val.map some ⦄ := by
  unfold runtime.compiler.collect_functions_loop
  apply loop.spec_decr_nat (fun state => original.length - state.2.2.2.1.val)
    (fun state => state.2.1.val.length = original.length ∧ state.2.2.2.1.val ≤ original.length ∧
      (state.2.2.2.2 = .Ok () → CollectionPrefix original state.2.1 state.2.2.1 state.2.2.2.1.val))
  · rintro ⟨currentBudget, currentPending, currentFunctions, currentIndex, status⟩ ⟨length, bound, prefixInvariant⟩
    dsimp only at length bound prefixInvariant
    unfold runtime.compiler.collect_functions_loop.body
    dsimp only
    split
    · rename_i more
      have inbounds : currentIndex.val < currentPending.val.length := by scalar_tac
      have originalBound : currentIndex.val < original.length := by omega
      cases status with
      | Err error => simp [core.result.Result.is_ok]
      | Ok acceptedUnit =>
        cases acceptedUnit
        obtain ⟨collected, remaining⟩ := prefixInvariant rfl
        have collectedLength := congrArg List.length collected
        simp only [List.length_take, List.length_map, Nat.min_eq_left bound] at collectedLength
        have capacity : currentFunctions.val.length < Usize.max := by
          have := currentPending.property
          omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with runtime.compiler.take_function.total allocator law currentBudget currentPending currentIndex currentFunctions
          inbounds capacity as ⟨nextStatus, nextBudget, nextPending, nextFunctions, sameLength, taken⟩
        step as ⟨nextIndex, nextEq⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact sameLength.trans length
        · scalar_tac
        · intro success
          obtain ⟨function, found, pendingEq, appended⟩ := taken success
          have lookup := congrArg (fun values => values[0]?) remaining
          simp only [List.getElem?_drop, Nat.add_zero] at lookup
          have originalFound : original[currentIndex.val]? = some (some function) := lookup.symm.trans found
          have element := (List.getElem?_eq_some_iff.mp originalFound).2
          constructor
          · rw [nextEq, List.take_succ_eq_append_getElem originalBound, element, collected, appended]
            simp
          · rw [nextEq, pendingEq, List.drop_set_of_lt (Nat.lt_succ_self _)]
            have tail := congrArg (List.drop 1) remaining
            simpa only [List.drop_drop] using tail
        · scalar_tac
    · rename_i finished
      have indexEnd : currentIndex.val = original.length := by scalar_tac
      simp only [WP.spec_ok]
      intro success
      obtain ⟨collected, _⟩ := prefixInvariant success
      simpa only [indexEnd, List.take_length] using collected
  · exact ⟨length, bound, invariant⟩


theorem _root_.Itasca.runtime.compiler.collect_functions.total {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)) :
    runtime.compiler.collect_functions allocator budget pending ⦃ (status, afterBudget, afterPending) =>
      ∀ functions, status = .Ok functions → pending.val = functions.val.map some ⦄ := by
  unfold runtime.compiler.collect_functions
  step with runtime.compiler.collect_functions_loop.total allocator law pending.val budget pending
    (alloc.vec.Vec.new _) 0#usize (.Ok ()) rfl (by simp)
    (by simp [CollectionPrefix, alloc.vec.Vec.new]) as ⟨afterBudget, afterPending, functions, status, collected⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok acceptedUnit =>
    cases acceptedUnit
    simp [core.result.Result.Insts.CoreOpsTry.branch, collected rfl]


theorem _root_.Itasca.runtime.compiler.take_function.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (function : runtime.bytecode.CompiledFunction)
    (inside : index.val < pending.val.length) (found : pending.val[index.val]? = some (some function))
    (capacity : functions.length < Usize.max) (reserve : functions.length+1 ≤ bound) :
    runtime.compiler.take_function ops budget pending index functions ⦃ (status, afterBudget, afterPending, afterFunctions) => status = .Ok () ∧ afterBudget = budget ∧
      afterPending.val = pending.val.set index.val none ∧ afterFunctions.val = functions.val++[function] ⦄ := by
  unfold runtime.compiler.take_function
  step as ⟨value,back,lookup,restore⟩
  have element : pending.val[index.val] = some function := (List.getElem?_eq_some_iff.mp found).2
  have valueEq : value = some function := lookup.trans element
  simp only [valueEq,element,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound allocation budget functions function capacity reserve
    as ⟨reply,afterBudget,afterFunctions,status,budgetEq,appended⟩
  subst reply afterBudget
  simp only [WP.spec_ok,restore,alloc.vec.Vec.set_val_eq]
  exact ⟨rfl,rfl,by simp only [alloc.vec.Vec.set_val_eq],appended⟩


theorem _root_.Itasca.runtime.compiler.collect_functions_loop.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ pending.length) (collected : functions.length = index.val)
    (reserve : pending.length ≤ bound)
    (populated : ∀ next, index.val ≤ next → next < pending.length → ∃ function, pending.val[next]? = some (some function)) :
    runtime.compiler.collect_functions_loop ops budget pending functions index (.Ok ()) ⦃ (afterBudget, afterPending, afterFunctions, status) =>
      status = .Ok () ∧ afterBudget = budget ⦄ := by
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
      step with runtime.compiler.take_function.available ops bound allocation budget currentPending currentIndex currentFunctions function
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


theorem _root_.Itasca.runtime.compiler.collect_functions.available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (reserve : pending.length ≤ bound)
    (populated : ∀ index, index < pending.length → ∃ function, pending.val[index]? = some (some function)) :
    runtime.compiler.collect_functions ops budget pending ⦃ (status, afterBudget, afterPending) => afterBudget = budget ∧
      ∃ functions, status = .Ok functions ∧ pending.val = functions.val.map some ⦄ := by
  have normal : runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧ ∃ functions, out.1 = .Ok functions ⦄ := by
    unfold runtime.compiler.collect_functions
    step with runtime.compiler.collect_functions_loop.available ops bound allocation budget pending (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp [alloc.vec.Vec.new]) reserve (by intro index _ bound; exact populated index bound)
      as ⟨afterBudget,afterPending,functions,status,accepted,same⟩
    subst status afterBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨True.intro,functions,rfl⟩
  obtain ⟨⟨reply,afterBudget,afterPending⟩,called,same,functions,accepted⟩ := WP.spec_imp_exists normal
  dsimp only at same accepted
  have ordered := runtime.compiler.collect_functions.total ops law budget pending
  rw [called,WP.spec_ok] at ordered ⊢
  exact ⟨same,functions,accepted,ordered functions accepted⟩


/-- Accepted extraction has exactly the pending-slot and ordered-append effect
proved by the total primitive contract. -/
theorem _root_.Itasca.runtime.compiler.take_function.inv {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (inside : index.val < pending.val.length) (capacity : functions.val.length < Usize.max)
    {output} (called : runtime.compiler.take_function ops budget pending index functions = .ok output) :
    let (status, _, afterPending, afterFunctions) := output
    afterPending.val.length = pending.val.length ∧
      (status = .Ok () → ∃ function,
        pending.val[index.val]? = some (some function) ∧
        afterPending.val = pending.val.set index.val none ∧
        afterFunctions.val = functions.val ++ [function]) := by
  have effect := runtime.compiler.take_function.total ops law budget pending index functions inside capacity
  rw [called, WP.spec_ok] at effect
  exact effect

/-- Successful loop completion preserves the complete original source order. -/
theorem _root_.Itasca.runtime.compiler.collect_functions_loop.inv {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (original : List (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (status : core.result.Result Unit runtime.compiler.CompileError)
    (length : pending.val.length = original.length) (inside : index.val ≤ original.length)
    (invariant : status = .Ok () → CollectionPrefix original pending functions index.val)
    {output} (called : runtime.compiler.collect_functions_loop ops budget pending functions index status = .ok output) :
    let (_, _, afterFunctions, reply) := output
    reply = .Ok () → original = afterFunctions.val.map some := by
  have effect := runtime.compiler.collect_functions_loop.total ops law original budget pending functions index status length inside invariant
  rw [called, WP.spec_ok] at effect
  exact effect

/-- A normally accepted collection contains exactly the original pending slots. -/
theorem _root_.Itasca.runtime.compiler.collect_functions.inv {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    {output} (called : runtime.compiler.collect_functions ops budget pending = .ok output) :
    let (status, _, _) := output
    ∀ functions, status = .Ok functions → pending.val = functions.val.map some := by
  have effect := runtime.compiler.collect_functions.total ops law budget pending
  rw [called, WP.spec_ok] at effect
  exact effect

end Itasca.Runtime.Compiler
