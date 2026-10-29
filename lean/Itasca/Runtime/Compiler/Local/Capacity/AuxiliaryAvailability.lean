import Itasca.Runtime.Compiler.Local.Capacity.CallbackAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A source-bounded auxiliary index passes the executable u32 gate. -/
theorem bounded_index_available (value : Usize) (bounded : value.val ≤ U32.max) :
    runtime.compiler.bounded_index value ⦃ out =>
      ∃ index, out = .Ok index ∧ index.val = value.val ⦄ := by
  unfold runtime.compiler.bounded_index
  step as ⟨maximum,maximumEq⟩
  have inside : ¬ value > maximum := by
    simp_all [core.num.U32.MAX,U32.rMax]
    scalar_tac
  simp only [if_neg inside]
  step as ⟨index,indexEq⟩
  refine ⟨index,rfl,?_⟩
  simp only [indexEq,UScalar.cast_val_eq]
  scalar_tac

/-- Pair-table insertion accepts its independently bounded index and reserve
request. Its exact append is retained for indirect-call and bulk-table code. -/
theorem compiler_pair_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (first second : U32)
    (indexBound : compiler.function.indirect.length ≤ U32.max)
    (capacity : compiler.function.indirect.length < Usize.max)
    (request : compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.pair ops compiler first second ⦃ out =>
      ∃ index pairs, out.1 = .Ok index ∧ index.val = compiler.function.indirect.length ∧
        out.2 = {compiler with function := {compiler.function with indirect := pairs}} ∧
        pairs.val = compiler.function.indirect.val ++ [(first,second)] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pair
  step with bounded_index_available (alloc.vec.Vec.len compiler.function.indirect) indexBound
    as ⟨status,index,accepted,indexEq⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available compiler.budget compiler.function.indirect
    (first,second) capacity request as ⟨status,budget,pairs,accepted,same,appended⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  exact ⟨index,pairs,rfl,indexEq,by rw [same],appended⟩

end Itasca.Runtime.Code
