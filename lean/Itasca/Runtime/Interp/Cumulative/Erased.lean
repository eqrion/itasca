import Itasca.Runtime.Interp.Core.Erased
import Itasca.Runtime.Interp.Core.OwnershipClosure
import Itasca.Runtime.Abs.Stateful.OwnershipStore
import Itasca.Runtime.Interp.StructuredMachine.SyntaxClosure
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Step
namespace Itasca.Runtime.Interp

theorem FrameOwnershipClosure.stateful {before after} (closure : FrameOwnershipClosure before after)
    {bounds s ambient rest} (owned : Abs.Ownership.StatefulOwned bounds ⟨s,ambient,before::rest,[]⟩) :
    Abs.Ownership.StatefulOwned bounds ⟨s,ambient,after::rest,[]⟩ := by
  refine ⟨⟨owned.values.1,?_⟩,owned.heap⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact closure bounds (owned.values.2 _ (List.mem_cons_self ..))
  · exact owned.values.2 frame (List.mem_cons_of_mem _ member)

end Itasca.Runtime.Interp
