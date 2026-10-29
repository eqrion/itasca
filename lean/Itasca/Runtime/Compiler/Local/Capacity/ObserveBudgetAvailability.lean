import Itasca.Runtime.Compiler.Local.Capacity.ObserveAvailability

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Available stack observation leaves the complete compilation budget intact,
including every resource counter and any earlier error marker. -/
theorem compiler_observe_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have initial : (if compiler.reachable then do
      let maximum ← lift (core.cmp.impls.OrdUsize.max compiler.function.max_stack (alloc.vec.Vec.len state.vals))
      .ok ({compiler.function with max_stack := maximum},state)
    else .ok (compiler.function,state)) ⦃ out =>
      out.1.local_slots = compiler.function.local_slots ∧ out.2 = state ⦄ := by
    split <;> step* <;> simp
  unfold runtime.compiler.FunctionCompiler.observe
  apply WP.spec_bind initial
  rintro ⟨function,otherState⟩ ⟨locals,sameState⟩
  dsimp only at locals sameState
  subst otherState
  step with runtime_clear compiler.before as ⟨cleared,empty⟩
  have capacity : cleared.length + (alloc.vec.Vec.deref state.vals).val.length ≤ Usize.max := by
    simpa [alloc.vec.Vec.length,empty,alloc.vec.Vec.deref] using state.vals.property
  have reserve : cleared.length + (alloc.vec.Vec.deref state.vals).val.length ≤ bound := by
    simpa [alloc.vec.Vec.length,empty,alloc.vec.Vec.deref] using request
  have words : function.local_slots.val + 2*(alloc.vec.Vec.deref state.vals).val.length ≤ U32.max := by
    simpa [locals,alloc.vec.Vec.deref] using slotsFit
  step with observe_values_available ops bound available compiler.budget cleared function.local_slots
    (alloc.vec.Vec.deref state.vals) 0#usize (by simp) (by simpa using capacity)
    (by simpa using reserve) (by simpa using words)
    as ⟨status,budget,offsets,height,accepted,same,count,wordBound⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  split
  · step as ⟨maximum,maximumEq⟩
    exact same
  · exact WP.spec.ret ⟨rfl,same⟩


end Itasca.Runtime.Compiler
