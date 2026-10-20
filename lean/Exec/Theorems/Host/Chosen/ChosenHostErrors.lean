import Exec.Theorems.Composition.Eventful.ChosenEventfulErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

theorem HostPreparationCause.chosen_eventful_error {choices : SourceChoices} (occurrence : Nat)
    {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {signature : Itasca.types.FuncType} {base : Usize} {source : Abs.AState} {error : runtime.ExecError}
    (cause : HostPreparationCause allocator hooks exec store platform signature base error) (typed : Abs.ATyped source) :
    ChosenEventfulInvocationError choices occurrence (Abs.decode source) [] source.store source.ambient error := by
  have kind := cause.error
  cases error <;> first
    | exact ⟨_,0,ChosenStepsN.refl occurrence typed.decode_wf⟩
    | simp [HostPreparationError] at kind

theorem host_frame_chosen_eventful_error {choices : SourceChoices} {occurrence count : Nat}
    {M P : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {initial : config} {events : List HostEvent} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    {after : List instr} {front : List val}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (kind : out.1=.Ok () ∨ out.1=.Err (.Trap .Host) ∨ out.1=.Err (.Exhausted .CallStack))
    (steps : ChosenStepsN choices occurrence count initial events (hostCallFrameResult view code ambient f rest after front out))
    {error : runtime.ExecError} (failed : out.1=.Err error) :
    ChosenEventfulInvocationError choices occurrence initial events (Store.decodeStore view code out.2.2.1) ambient error := by
  rcases kind with success | trapped | exhausted
  · rw [success] at failed
    cases failed
  · have same : error=.Trap .Host := by simpa only [failed,core.result.Result.Err.injEq] using trapped
    subst error
    exact ⟨count,by simpa only [hostCallFrameResult,failed] using steps⟩
  · have same : error=.Exhausted .CallStack := by simpa only [failed,core.result.Result.Err.injEq] using exhausted
    subst error
    exact ⟨[.TRAP],count,by simpa only [hostCallFrameResult,failed] using steps⟩
end Exec.Theorems
