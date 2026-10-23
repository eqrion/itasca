import Exec.Interp.StructuredMachine.Advance
import Exec.Interp.Machines.Uniform.UniformControl
import Exec.Abs.Stateful.OwnershipStore
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- The existing mutable advance, with the same endpoint and a uniform silent rank. -/
def UniformAdvance
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    UniformConcreteSim pc nextPC pending nextPending before after [] ∧
    (∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)

variable  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : Abs.AState}

theorem UniformAdvance.forget
    (step : UniformAdvance view code store exec expected codeLength pc pending before) :
    Advance view code store exec expected codeLength pc pending before := by
  obtain ⟨nextPC,nextPending,after,machine,simulation,uniform,ownership,ambient,bounded⟩ := step
  exact ⟨nextPC,nextPending,after,machine,simulation,ownership,ambient,bounded⟩

theorem UniformAdvance.of_frame_forward {nextPC : Aeneas.Std.U32} {after : Abs.AState}
    (machine : Execution view code store exec after expected nextPC.val false)
    (simulation : ConcreteSim codeLength pc nextPC.val false false before after)
    (forward : pc < nextPC.val)
    (ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    UniformAdvance view code store exec expected codeLength pc false before :=
  ⟨nextPC.val,false,after,machine,simulation,
    simulation.uniform_forward forward (by scalar_tac),ownership,ambient,bounded⟩

end Exec.Interp.StructuredMachine
