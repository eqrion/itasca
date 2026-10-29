import Itasca.Runtime.Compiler.Local.Initializer.InitializerComplete
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Support.EnvTranslation
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Moving a successful function into the dense executable vector preserves
its source slot and appends precisely that function. -/
@[step] theorem take_function_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (bound : index.val < pending.val.length) (capacity : functions.val.length < Usize.max) :
    runtime.compiler.take_function allocator budget pending index functions ⦃ out =>
      out.2.2.1.val.length = pending.val.length ∧
      (out.1 = .Ok () → ∃ function,
        pending.val[index.val]? = some (some function) ∧
        out.2.2.1.val = pending.val.set index.val none ∧
        out.2.2.2.val = functions.val ++ [function]) ⦄ := by
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
      refine ⟨True.intro, fun _ => ⟨function, ?_, True.intro, appended⟩⟩
      rw [List.getElem?_eq_getElem bound, ← lookup]
    · simp [restore, alloc.vec.Vec.set_val_eq]

/-- The pending suffix retains its source indices; the output is exactly the
already collected prefix, with no missing, duplicate, or reordered function. -/
def CollectionPrefix (original : List (Option runtime.bytecode.CompiledFunction))
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Nat) : Prop :=
  original.take index = functions.val.map some ∧ pending.val.drop index = original.drop index

@[step] theorem collect_functions_loop_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (original : List (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (result : core.result.Result Unit runtime.compiler.CompileError)
    (length : pending.val.length = original.length) (bound : index.val ≤ original.length)
    (invariant : result = .Ok () → CollectionPrefix original pending functions index.val) :
    runtime.compiler.collect_functions_loop allocator budget pending functions index result ⦃ out =>
      out.2.2.2 = .Ok () → original = out.2.2.1.val.map some ⦄ := by
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
        step with take_function_spec allocator law currentBudget currentPending currentIndex currentFunctions
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

/-- Actual collection succeeds exactly in source order. The final pending
vector is internal; callers receive the dense vector with every original slot. -/
@[step] theorem collect_functions_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)) :
    runtime.compiler.collect_functions allocator budget pending ⦃ out =>
      ∀ functions, out.1 = .Ok functions → pending.val = functions.val.map some ⦄ := by
  unfold runtime.compiler.collect_functions
  step with collect_functions_loop_spec allocator law pending.val budget pending
    (alloc.vec.Vec.new _) 0#usize (.Ok ()) rfl (by simp)
    (by simp [CollectionPrefix, alloc.vec.Vec.new]) as ⟨afterBudget, afterPending, functions, status, collected⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok acceptedUnit =>
    cases acceptedUnit
    simp [core.result.Result.Insts.CoreOpsTry.branch, collected rfl]

end Itasca.Runtime.Compiler
