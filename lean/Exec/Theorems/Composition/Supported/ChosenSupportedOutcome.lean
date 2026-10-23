import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.SupportedChosenAdvance
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
def ChosenCumulativeFailure (choices : Spec.SourceChoices) (occurrence : Nat) {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : Abs.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap,error=.Trap trap ∧ CumulativeTrap trap) ∧ ∃ n,0<n ∧ Spec.ChosenStepsN choices occurrence n (Abs.decode source) []
    ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩) ∨
  (error=.Terminated ∧ ∃ after,hooks.interrupt platform=.ok (.Terminate,after)) ∨
  ∃ index raw inst compiled,
    index.val+1=exec.frames.length ∧ exec.frames.val[index.val]?=some raw ∧
    store.instances.val[raw.instance.val]?=some inst ∧ inst.module.functions.val[raw.function.val]?=some compiled ∧
    (SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error ∨
      ∃ code, SourceIndirectCallCause allocator hooks code exec store platform index raw compiled source error)


/-- Concrete mutation evidence and the full source/machine outcome of one
cumulative dispatch. Fresh certification follows from the mutation witness. -/
def ChosenSupportedStepOutcome (choices : Spec.SourceChoices) (occurrence : Nat) {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : Abs.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CumulativeStoreMutation view code store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => StructuredMachine.ChosenAdvance choices occurrence view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => ChosenCumulativeFailure choices occurrence allocator hooks exec store platform source error ∧
      Store.decodeStore view code out.2.2.1=source.store

variable {choices : Spec.SourceChoices} {occurrence : Nat} {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem ChosenSupportedStepOutcome.success (mutation : CumulativeStoreMutation view code store out.2.2.1)
    (status : out.1=.Ok ())
    (advance : StructuredMachine.ChosenAdvance choices occurrence view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using advance⟩

theorem ChosenSupportedStepOutcome.unchanged_success (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (same : out.2.2.1=store) (status : out.1=.Ok ())
    (advance : StructuredMachine.ChosenAdvance choices occurrence view code store out.2.1 expected codeLength pc pending source) :
    ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply ChosenSupportedStepOutcome.success (by rw [same]; exact .refl_of_shape shaped sourceSyntax bounds) status
  simpa only [same] using advance

theorem ChosenSupportedStepOutcome.failure (mutation : CumulativeStoreMutation view code store out.2.2.1)
    {error : runtime.ExecError} (status : out.1=.Err error)
    (decoded : Store.decodeStore view code out.2.2.1=source.store)
    (cause : ChosenCumulativeFailure choices occurrence allocator hooks exec store platform source error) :
    ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using And.intro cause decoded⟩

end Exec.Theorems
