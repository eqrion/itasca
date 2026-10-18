import Exec.Theorems.Composition.InstantiationResult
import Exec.Theorems.Instantiation.TailCore
import Exec.Theorems.Instantiation.StartCoreReachable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem checked_results_conjoin {α : Type} {run : Result α} {p q : α → Prop}
    (left : WP.dspec run p) (right : WP.dspec run q) : WP.dspec run (fun out => p out ∧ q out) := by
  cases left with
  | ret satisfied => exact .ret ⟨satisfied, by simpa only [WP.dspec_ok] using right⟩
  | div => exact .div _

theorem StoreReachable.prepend_steps {initial next : config} {store : _root_.store}
    (reachable : StoreReachable next store) (steps : StepsH initial [] next) : StoreReachable initial store := by
  obtain ⟨ambient,body,tail⟩ := reachable
  exact ⟨ambient,body,Spec.stepsH_trans steps tail⟩

theorem TailCoreSourceResult.initialized_execution_same {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {inst : runtime.store.Instance} {store : runtime.store.Store M}
    {identity : runtime.InstanceAddr} {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (outcome : TailCoreSourceResult view code inst store store identity (.Ok ()) result)
    (initial : config)
    (initialSteps : StepsH initial [] ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩,
      (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList⟩) :
    InstantiationExecution initial (Store.decodeStore view code store) (moduleStartFrame store inst) result := by
  rcases outcome with ⟨absent, returned⟩ | ⟨index, address, start, mapped, returns, errors⟩
  · subst result
    simpa only [InstantiationExecution, absent, Option.map_none, Option.toList_none] using initialSteps
  · have callPrefix : StepsH initial [] (moduleStartConfiguration view code store inst index) := by
      simpa only [start, Option.map_some, Option.toList_some, moduleStartConfiguration] using initialSteps
    cases result with
    | Ok address =>
      exact Spec.stepsH_trans callPrefix (returns address rfl).2
    | Err error =>
      have failed := errors error rfl
      cases error <;> simp only [CoreInvocationError, InstantiationExecution] at failed ⊢
      · exact Spec.stepsH_trans callPrefix failed.2
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
end Exec.Theorems
