import Exec.Theorems.Composition.Core.CoreInstantiationResult
import Exec.Theorems.Instantiation.TailExecutableCases
import Exec.Theorems.Instantiation.StartExecutableReachable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem TailExecutableSourceResult.initialized_execution_same {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {inst : runtime.store.Instance} {store : runtime.store.Store M}
    {identity : runtime.InstanceAddr} {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (outcome : TailExecutableSourceResult view code inst store store identity (.Ok ()) result)
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
      cases error <;> simp only [SupportedInvocationError, InstantiationExecution] at failed ⊢
      · exact Spec.stepsH_trans callPrefix failed.2
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
end Exec.Theorems
