import Exec.Code.Local.Callbacks.Common.Observe
namespace Exec.Code
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
end Exec.Code
