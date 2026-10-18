import Exec.Interp.Machines.Uniform.UniformSourceControl
namespace Exec.Interp
 theorem EventfulConcreteSim.uniform_of_events {codeLength beforePC afterPC beforePending afterPending before after events}
    (simulation : EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events)
    (nonempty : events ≠ []) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events := by
  rcases simulation with ⟨_,empty,_⟩ | positive
  · exact (nonempty empty).elim
  · exact Or.inr positive
end Exec.Interp
