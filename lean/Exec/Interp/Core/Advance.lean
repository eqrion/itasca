import Exec.Interp.Core.Execution
import Exec.Abs.Ownership.Core
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A returned mutable-machine step retains the complete current state,
source simulation and reference provenance for every initial issued bound. -/
def CoreAdvance {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    CoreExecution view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    (∀ bounds, Abs.Ownership.CoreOwned bounds before → Abs.Ownership.CoreOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

 theorem CoreAdvance.of_frame {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}
    {nextPC : U32} {nextPending : Bool} {after : Abs.AState}
    (machine : CoreExecution view code store exec after expected nextPC.val nextPending)
    (simulation : ConcreteSim codeLength pc nextPC.val pending nextPending before after)
    (ownership : ∀ bounds, Abs.Ownership.CoreOwned bounds before → Abs.Ownership.CoreOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    CoreAdvance view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,simulation,ownership,ambient,bounded⟩
end Exec.Interp
