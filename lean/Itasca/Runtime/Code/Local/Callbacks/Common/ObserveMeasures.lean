import Itasca.Runtime.Code.Local.Callbacks.Common.Observe
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
