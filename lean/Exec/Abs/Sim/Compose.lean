import Exec.Abs.Sim.Typed

namespace Exec.Abs
open Exec.Spec

/-- Fusing source administrative instructions preserves counted simulation.
Positive reductions compose; a decoding stutter contributes no source steps. -/
theorem NextSim.trans {first middle last : AState}
    (left : NextSim first middle) (right : NextSim middle last) : NextSim first last := by
  rcases left with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · rcases right with ⟨same', decrease'⟩ | ⟨n, positive, steps⟩
    · exact Or.inl ⟨same.trans same', Nat.lt_trans decrease' decrease⟩
    · exact Or.inr ⟨n, positive, by simpa only [same] using steps⟩
  · rcases right with ⟨same', _⟩ | ⟨m, positive', steps'⟩
    · exact Or.inr ⟨n, positive, by simpa only [same'] using steps⟩
    · exact Or.inr ⟨n + m, by omega, by simpa only [List.nil_append] using steps.trans steps'⟩

end Exec.Abs
