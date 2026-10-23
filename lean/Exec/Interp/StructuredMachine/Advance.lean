import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Ownership.Core
import Exec.Abs.Stateful.OwnershipStore
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- A returned mutable-machine step retains the complete current state,
source simulation and reference provenance for every initial issued bound. -/
def Advance
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    (∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

 theorem Advance.of_frame  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}
    {nextPC : U32} {nextPending : Bool} {after : Abs.AState}
    (machine : Execution view code store exec after expected nextPC.val nextPending)
    (simulation : ConcreteSim codeLength pc nextPC.val pending nextPending before after)
    (ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    Advance view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,simulation,ownership,ambient,bounded⟩
end Exec.Interp.StructuredMachine
