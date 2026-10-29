import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe

/-!
Frame and resource-measure preservation for compiler observation, used by callback capacity proofs.
-/

/-! ## Observe Frame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Observation changes only compiler work state and allocation high-water marks. -/
def ObserveFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = { before with budget := after.budget, before := after.before, height := after.height, next_source := after.next_source, function := { before.function with max_stack := after.function.max_stack, slot_count := after.function.slot_count } }

@[step] theorem compiler_observe_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [ObserveFrame, core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
end Itasca.Runtime.Compiler

end

/-! ## Observe Measures -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- High-water marks are exactly the maxima of previously observed capacity
and the current validator stack; dead source positions do not increase them. -/
@[step] theorem compiler_observe_measures {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () →
        out.2.function.max_stack.val = (if compiler.reachable then
          max compiler.function.max_stack.val state.vals.val.length else compiler.function.max_stack.val) ∧
        out.2.function.slot_count.val = (if compiler.reachable then
          max compiler.function.slot_count.val (observedHeight compiler.function.local_slots.val state.vals.val)
          else compiler.function.slot_count.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [core.cmp.impls.OrdUsize.max, core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals scalar_tac
end Itasca.Runtime.Compiler

end
