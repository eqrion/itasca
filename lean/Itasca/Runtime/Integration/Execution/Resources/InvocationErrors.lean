import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Interp.Machine.Outcomes.ScalarTraps
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Retention.StatefulOwnership
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Host.HostReturnFrames
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Integration.Host.HostCallContext

/-!
Sections, each formerly its own module: Failure, FailureNormalization, FailureErrors, InvocationErrors.
-/

/-! ## Failure -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

def CumulativeTrap (trap : runtime.Trap) : Prop := FloatCoreTrap trap ∨ trap = .TableOutOfBounds ∨ trap = .UninitializedElement ∨ trap = .IndirectCallTypeMismatch

def CumulativeFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : SourceMachine.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap,error=.Trap trap ∧ CumulativeTrap trap) ∧ ∃ n,0<n ∧ Spec.StepsHN n (SourceMachine.decode source) []
    ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩) ∨
  (error=.Terminated ∧ ∃ after,hooks.interrupt platform=.ok (.Terminate,after)) ∨
  ∃ index raw inst compiled,
    index.val+1=exec.frames.length ∧ exec.frames.val[index.val]?=some raw ∧
    store.instances.val[raw.instance.val]?=some inst ∧ inst.module.functions.val[raw.function.val]?=some compiled ∧
    (SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error ∨
      ∃ code, SourceIndirectCallCause allocator hooks code exec store platform index raw compiled source error)

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : SourceMachine.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

end Itasca.Runtime.Integration

end

/-! ## FailureNormalization -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem CumulativeFailure.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : SourceMachine.AFrame} {s : _root_.store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s, ambient, before :: rest, []⟩)
    (failure : CumulativeFailure allocator hooks exec store platform ⟨s, ambient, middle :: rest, []⟩ error) :
    CumulativeFailure allocator hooks exec store platform ⟨s, ambient, before :: rest, []⟩ error := by
  rcases failure with ⟨kind, n, positive, steps⟩ | interrupted | rejected
  · refine Or.inl ⟨kind, ?_⟩
    rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
    · exact ⟨n, positive, by simpa only [same] using steps⟩
    · rcases simulation with ⟨same, _⟩ | ⟨m, hm, reductions⟩
      · exact ⟨n, positive, by simpa only [same] using steps⟩
      · exact ⟨m + n, by omega, by simpa using reductions.trans steps⟩
  · exact Or.inr (Or.inl interrupted)
  · obtain ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, cause⟩ := rejected
    refine Or.inr (Or.inr ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, ?_⟩)
    have counted : ∃ n, Spec.StepsHN n (SourceMachine.decode ⟨s, ambient, before :: rest, []⟩) []
        (SourceMachine.decode ⟨s, ambient, middle :: rest, []⟩) := by
      rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
      · subst middle
        exact ⟨0, .refl typed.decode_wf⟩
      · rcases simulation with ⟨same, _⟩ | ⟨n, positive, reductions⟩
        · exact ⟨0, by rw [← same]; exact .refl typed.decode_wf⟩
        · exact ⟨n, reductions⟩
    obtain ⟨n, steps⟩ := counted
    rcases cause with direct | ⟨code,indirect⟩
    · exact Or.inl (direct.prepend steps rfl rfl)
    · exact Or.inr ⟨code,indirect.prepend steps rfl rfl⟩

end Itasca.Runtime.Integration

end

/-! ## FailureErrors -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Every Core integer, control, global, and memory trap has a positive checked source execution to
`TRAP`; boundary and resource failures cannot masquerade as traps. -/
theorem CumulativeFailure.trap {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {trap : runtime.Trap}
    (failure : CumulativeFailure allocator hooks exec store platform source (.Trap trap)) :
    CumulativeTrap trap ∧ ∃ count, 0 < count ∧
      Spec.StepsHN count (SourceMachine.decode source) [] ⟨⟨source.store, source.ambient⟩, [.TRAP]⟩ := by
  rcases failure with ⟨kind, reductions⟩ | ⟨kind, interrupted⟩ | rejected
  · obtain ⟨actual, same, allowed⟩ := kind
    cases same
    exact ⟨allowed, reductions⟩
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · simpa using direct.concrete.kind
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      simpa using cause.kind

/-- No other runtime error class is reachable in the verified Core machine. -/
theorem CumulativeFailure.kind {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {error : runtime.ExecError}
    (failure : CumulativeFailure allocator hooks exec store platform source error) :
    (∃ trap, error = .Trap trap ∧ CumulativeTrap trap) ∨ error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  rcases failure with ⟨kind, _⟩ | ⟨kind, _⟩ | rejected
  · exact Or.inl kind
  · exact Or.inr (Or.inl kind)
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · exact Or.inr direct.concrete.kind
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      exact Or.inr cause.kind

end Itasca.Runtime.Integration

end

/-! ## InvocationErrors -/

section

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
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.wasm_types.FuncType} {base : Usize}
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

end
