import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.SupportedAdvance
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
/-- Concrete mutation evidence and the full source/machine outcome of one
cumulative dispatch. Fresh certification follows from the mutation witness. -/
def SupportedStepOutcome (emission : StructuredMachine.FunctionEmission) (allowed : instr → Prop) {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : Abs.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CumulativeStoreMutation view code store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => StructuredMachine.Advance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => CumulativeFailure allocator hooks exec store platform source error ∧
      Store.decodeStore view code out.2.2.1=source.store

variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem SupportedStepOutcome.success (mutation : CumulativeStoreMutation view code store out.2.2.1)
    (status : out.1=.Ok ())
    (advance : StructuredMachine.Advance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using advance⟩

theorem SupportedStepOutcome.unchanged_success (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (same : out.2.2.1=store) (status : out.1=.Ok ())
    (advance : StructuredMachine.Advance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store out.2.1 expected codeLength pc pending source) :
    SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply SupportedStepOutcome.success (by rw [same]; exact .refl_of_shape shaped sourceSyntax bounds) status
  simpa only [same] using advance

theorem SupportedStepOutcome.failure (mutation : CumulativeStoreMutation view code store out.2.2.1)
    {error : runtime.ExecError} (status : out.1=.Err error)
    (decoded : Store.decodeStore view code out.2.2.1=source.store)
    (cause : CumulativeFailure allocator hooks exec store platform source error) :
    SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using And.intro cause decoded⟩

end Exec.Theorems
