import Exec.Interp.StructuredMachine.UniformAdvance
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
theorem UniformAdvance.of_frame  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype}
    {codeLength pc : Nat} {pending nextPending : Bool} {before after : Abs.AState} {nextPC : U32}
    (machine : Execution view code store exec after expected nextPC.val nextPending)
    (simulation : ConcreteSim codeLength pc nextPC.val pending nextPending before after)
    (uniform : UniformConcreteSim pc nextPC.val pending nextPending before after [])
    (ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds before → Abs.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) :
    UniformAdvance view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,simulation,uniform,ownership,ambient,bounded⟩
end Exec.Interp.StructuredMachine
