import Exec.Theorems.Instantiation.InstantiateTailSlice
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Completed and trapped instantiations execute to the corresponding source
result. Exhaustion or interruption retains a reachable configuration with the
actual final store. The prefix may stop before a start call. -/
def InstantiationExecution (initial : config) (store : _root_.store) (ambient : frame) :
    core.result.Result runtime.InstanceAddr runtime.ExecError → Prop
  | .Ok _ => StepsH initial [] ⟨⟨store, ambient⟩, []⟩
  | .Err (.Trap _) => StepsH initial [] ⟨⟨store, ambient⟩, [.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated =>
    ∃ frame body, StepsH initial [] ⟨⟨store, frame⟩, body⟩
  | .Err _ => False

/-- Successful segment initialization composes with the actual optional start
outcome; all start error prefixes retain the initialized store. -/
theorem TailSourceResult.initialized_execution {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {inst : runtime.store.ModuleInst} {store : runtime.store.Store M}
    {identity : runtime.InstanceAddr} {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (outcome : TailSourceResult view code inst store identity (.Ok ()) result)
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
      cases error <;> simp only [SliceInvocationError, InstantiationExecution] at failed ⊢
      · exact Spec.stepsH_trans callPrefix failed.2
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
      · exact ⟨moduleStartFrame store inst, [.CALL (.mk_uN index.val)], callPrefix⟩
end Exec.Theorems
