import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Step

/-!
Extending frame ownership closure to stateful source states.

Main declarations: `FrameOwnershipClosure.stateful`. A direct consumer is `Interp.Machine.Coverage.SupportedControlSemantics`.
-/

namespace Itasca.Runtime.Interp

theorem FrameOwnershipClosure.stateful {before after} (closure : FrameOwnershipClosure before after)
    {bounds s ambient rest} (owned : SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.Ownership.StatefulOwned bounds ⟨s,ambient,after::rest,[]⟩ := by
  refine ⟨⟨owned.values.1,?_⟩,owned.heap⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact closure bounds (owned.values.2 _ (List.mem_cons_self ..))
  · exact owned.values.2 frame (List.mem_cons_of_mem _ member)

end Itasca.Runtime.Interp
