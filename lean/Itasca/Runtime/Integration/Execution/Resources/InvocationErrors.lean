import Itasca.Runtime.Integration.Execution.Resources.FailureErrors
import Itasca.Runtime.Interp.Host.HostPreparationCauses
import Itasca.Runtime.Spec.Counted
import Itasca.Runtime.Integration.Host.HostCallContext
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Source outcomes for errors after checked invocation entry. Resource and
interrupt cases retain the exact reached store, including callback effects;
local cause theorems separately constrain why those errors were chosen. -/
def EventfulInvocationError (initial : config) (events : List HostEvent)
    (store : _root_.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap _ => StepsH initial events ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => ∃ body, StepsH initial events ⟨⟨store,ambient⟩,body⟩
  | _ => False

theorem EventfulInvocationError.prepend {initial middle : config} {events rest : List HostEvent}
    {store : _root_.store} {ambient : frame} {error : runtime.ExecError}
    (outcome : EventfulInvocationError middle rest store ambient error)
    (prefixSteps : StepsH initial events middle) :
    EventfulInvocationError initial (events++rest) store ambient error := by
  cases error <;> simp only [EventfulInvocationError] at outcome ⊢
  · exact Spec.steps_h_trans prefixSteps outcome
  · obtain ⟨body,steps⟩ := outcome
    exact ⟨body,Spec.steps_h_trans prefixSteps steps⟩
  · obtain ⟨body,steps⟩ := outcome
    exact ⟨body,Spec.steps_h_trans prefixSteps steps⟩

theorem EventfulInvocationError.reachable {initial : config} {events : List HostEvent}
    {store : _root_.store} {ambient : frame} {error : runtime.ExecError}
    (outcome : EventfulInvocationError initial events store ambient error) :
    ∃ body, StepsH initial events ⟨⟨store,ambient⟩,body⟩ := by
  cases error <;> simp only [EventfulInvocationError] at outcome
  · exact ⟨[.TRAP],outcome⟩
  · exact outcome
  · exact outcome

theorem CumulativeFailure.eventful_error {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {error : runtime.ExecError}
    (failure : CumulativeFailure allocator hooks exec store platform source error)
    (typed : SourceMachine.ATyped source) :
    EventfulInvocationError (SourceMachine.decode source) [] source.store source.ambient error := by
  have kind := failure.kind
  cases error with
  | Trap trap => exact (failure.trap).2.choose_spec.2.erase
  | Exhausted limit => exact ⟨_,StepsH.refl typed.decode_wf⟩
  | Terminated => exact ⟨_,StepsH.refl typed.decode_wf⟩
  | BadArguments => simp at kind
  | Internal => simp at kind
  | WrongStore => simp at kind
  | Link reason => simp at kind

theorem HostPreparationCause.eventful_error {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.types.FuncType} {base : Usize}
    {source : SourceMachine.AState} {error : runtime.ExecError}
    (cause : HostPreparationCause allocator hooks exec store platform signature base error)
    (typed : SourceMachine.ATyped source) :
    EventfulInvocationError (SourceMachine.decode source) [] source.store source.ambient error := by
  have kind := cause.error
  cases error <;> first
    | exact ⟨_,StepsH.refl typed.decode_wf⟩
    | simp [HostPreparationError] at kind
/-- A callback trap or stack-overflow reply has a real labeled source endpoint;
its committed store effects survive even when the concrete API reports exhaustion. -/
theorem host_frame_eventful_error {M P : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {initial : config} {events : List HostEvent} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {after : List instr} {front : List val}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (kind : out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack))
    (steps : StepsH initial events (hostCallFrameResult view code ambient f rest after front out))
    {error : runtime.ExecError} (failed : out.1=.Err error) :
    EventfulInvocationError initial events (Store.decodeStore view code out.2.2.1) ambient error := by
  rcases kind with success | trapped | exhausted
  · rw [success] at failed
    cases failed
  · have same : error=.Trap .Host := by simpa only [failed,core.result.Result.Err.injEq] using trapped
    subst error
    simpa only [EventfulInvocationError,hostCallFrameResult,failed] using steps
  · have same : error=.Exhausted .CallStack := by simpa only [failed,core.result.Result.Err.injEq] using exhausted
    subst error
    refine ⟨[.TRAP],?_⟩
    simpa only [hostCallFrameResult,failed] using steps

end Itasca.Runtime.Integration
