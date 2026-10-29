import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Integration.Execution.Ownership.StoreOperations
import Itasca.Runtime.Interp.Relations.FrameStorePrefix

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- The raw function prefix retains function addresses. External-reference
issuance is a separate namespace absent from the decoded specification store,
so its monotonicity remains explicit in this conditional transport lemma. -/
theorem FrameStorePrefix.ownership_extension {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after)
    (externs : before.externs.length ≤ after.externs.length) :
    (Store.ownershipBounds before).Extends (Store.ownershipBounds after) := by
  refine ⟨?_,externs⟩
  have same := congrArg List.length retained.functions
  change (after.funcs.val.take before.funcs.val.length).length = before.funcs.val.length at same
  change before.funcs.val.length ≤ after.funcs.val.length
  rw [←same]
  simp only [List.length_take]
  exact Nat.min_le_right _ _

end Itasca.Runtime.Interp
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Checked returned values and fresh store shape restore all ownership facts
needed by the next interpreter iteration. The old caller's retained values
are transported through explicit raw namespace growth. -/
theorem host_return_stateful_owned {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} {ambient : frame} {caller : Abs.AFrame}
    {rest : List Abs.AFrame} {front args returned : List val} {continuation : List instr}
    (retained : FrameStorePrefix before after)
    (externs : before.externs.length ≤ after.externs.length)
    (shape : Store.Shape view after)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds before)
      ⟨Store.decodeStore view code before,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++args)
    (results : Abs.Ownership.ValuesOwned (Store.ownershipBounds after) returned) :
    Abs.Ownership.StatefulOwned (Store.ownershipBounds after)
      ⟨Store.decodeStore view code after,ambient,{caller with code:=continuation,vals:=front++returned}::rest,[]⟩ :=
  ⟨owned.host_return (retained.ownership_extension externs) split results,shape.stateful_heap_owned code⟩
end Itasca.Runtime.Theorems
