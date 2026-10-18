import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Ownership.Core
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- A returned mutable-machine step retains the complete current state,
source simulation and reference provenance for every initial issued bound. -/
def Advance (emission : FunctionEmission) (supported : Abs.AState → Prop)
    (owned : Abs.Ownership.Bounds → Abs.AState → Prop) {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution emission supported view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    (∀ bounds, owned bounds before → owned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

 theorem Advance.of_frame {emission supported owned} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}
    {nextPC : U32} {nextPending : Bool} {after : Abs.AState}
    (machine : Execution emission supported view code store exec after expected nextPC.val nextPending)
    (simulation : ConcreteSim codeLength pc nextPC.val pending nextPending before after)
    (ownership : ∀ bounds, owned bounds before → owned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    Advance emission supported owned view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,simulation,ownership,ambient,bounded⟩
end Exec.Interp.StructuredMachine
