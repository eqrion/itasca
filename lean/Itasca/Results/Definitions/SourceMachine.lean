import Aeneas
import SpecExt.Host
import «wasm2.0»

/-!
# Source execution vocabulary

Finite and infinite executions use SpecTec configurations and SpecExt host steps
directly. The private flat source machine and its representation invariants live
in Runtime/SourceMachine and are not needed to interpret these definitions.

-/

section SpecInitialization

/-!
## Bounded source initialization sequences

`StepsHN` counts host-aware source steps. Divergence requires positive chunks
so an infinite sequence cannot consist only of empty reflexive reductions.
-/

namespace Itasca.Spec

open SpecExt

inductive StepsHN : Nat → config → List HostEvent → config → Prop where
  | refl {c : config} : wf_config c → StepsHN 0 c [] c
  | cons {n : Nat} {c c' c'' : config} {events rest : List HostEvent} :
      StepH c events c' → StepsHN n c' rest c'' →
      StepsHN (n + 1) c (events ++ rest) c''

end Itasca.Spec

end SpecInitialization

section SpecSourceExecution

/-!
## Source invocation and initialization

The ambient invocation frame and coherent infinite reductions explain source
behavior without introducing a second execution-state representation.
-/

namespace Itasca.Spec

open SpecExt

/-- The generated invocation judgment fixes the ambient frame to the empty
module instance and emits the argument constants followed by CALL_ADDR. -/
def invocationFrame : frame := ⟨[], ⟨[], [], [], [], [], [], [], []⟩⟩

end Itasca.Spec

namespace Itasca.Spec

open SpecExt

/-- A coherent infinite source execution retaining the events in every positive
chunk. Empty event lists remain possible for arbitrarily long executions. -/
def InfiniteSourceWithEvents (initial : config) : Prop :=
  ∃ states : Nat → config, ∃ events : Nat → List HostEvent,
    states 0 = initial ∧ ∀ n, ∃ count, 0 < count ∧
      StepsHN count (states n) (events n) (states (n+1))

end Itasca.Spec

end SpecSourceExecution
