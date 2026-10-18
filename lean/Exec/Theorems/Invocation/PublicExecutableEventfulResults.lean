import Exec.Theorems.Invocation.PublicExecutableEventfulInvocation
import Exec.Theorems.Host.HostSegmentPublication
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Even when execution can call hosts, API rejection is confined to the
unchanged-state branch: checked execution cannot produce these error classes. -/
theorem ExecutableEventfulInvocationOutcome.api_rejection {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial out} (outcome : ExecutableEventfulInvocationOutcome view code before exec platform results initial out)
    {error : runtime.ExecError} (failed : out.1=.Err error)
    (kind : error=.BadArguments ∨ error=.WrongStore) :
    out=(.Err error,exec,before,platform,results) := by
  rcases outcome.2.2.2.2.2 error failed with early | ⟨events,executed⟩
  · exact early.2
  · rcases kind with rfl | rfl <;> cases executed

/-- Every returned reference can be passed to the issued-value API in the
resulting store, including references published by a reentrant host callback. -/
theorem ExecutableEventfulInvocationOutcome.returned_values {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial out} (outcome : ExecutableEventfulInvocationOutcome view code before exec platform results initial out)
    (success : out.1=.Ok ()) :
    ∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value :=
  (outcome.2.2.2.2.1 success).2

/-- Reentrant publication is counted by the appended instances' exact segment
maps. Existing instance mappings remain available under the raw prefix. -/
theorem ExecutableEventfulInvocationOutcome.segment_publication {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial out} (valid : ExecutableInv view code before)
    (outcome : ExecutableEventfulInvocationOutcome view code before exec platform results initial out) :
    Store.SegmentPublication before out.2.2.1 :=
  valid.segment_publication outcome.1 outcome.2.1
end Exec.Theorems
