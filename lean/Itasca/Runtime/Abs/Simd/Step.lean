import Itasca.Runtime.Abs.Simd.MemoryInvariants
import Itasca.Runtime.Abs.Simd.Constant

namespace Itasca.Runtime.Abs.Simd
open SpecExt Itasca.Runtime.Spec Ownership

/-- Relational SIMD execution, preserving source nondeterminism in pure results
and exact payload mutations for memory operations. -/
inductive Step : AState → AResult → Prop where
  | pure {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs output next}
      (signature : PureSignature source inputs output)
      (transition : Transition ⟨s,ambient,{f with code := source :: after}::rest,[]⟩
        {f with code := source :: after} rest after source inputs output next) :
      Step ⟨s,ambient,{f with code := source :: after}::rest,[]⟩ (.next next)
  | constant {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {value : vec_} :
      Step ⟨s,ambient,{f with code := .VCONST .V128 value :: after}::rest,[]⟩
        (.next (Simd.constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after}::rest,[]⟩ f rest after value))
  | memory {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs outputs result}
      (signature : MemorySignature source inputs outputs)
      (transition : MemoryTransition ⟨s,ambient,{f with code := source :: after}::rest,[]⟩
        {f with code := source :: after} rest after source inputs outputs result) :
      Step ⟨s,ambient,{f with code := source :: after}::rest,[]⟩ result

theorem Step.next_typed {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : CoreTyped next := by
  cases step with
  | pure signature transition => exact transition_core_typed signature typed transition
  | constant => exact constant_typed typed
  | memory signature transition => exact (memory_transition_preservation signature typed transition).1

theorem Step.next_simulation {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : NextSim before next := by
  cases step with
  | pure signature transition => exact transition_simulation signature typed.typed transition
  | constant => exact constant_simulation typed.typed
  | memory signature transition => exact memory_transition_simulation signature typed.typed transition

theorem Step.next_owned {before next bounds} (step : Step before (.next next))
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | pure signature transition => exact transition_owned signature owned transition
  | constant => exact constant_owned owned
  | memory signature transition => exact memory_transition_owned signature owned transition

theorem Step.next_bound {before next bound} (step : Step before (.next next))
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | pure signature transition => exact transition_bound bounded transition
  | constant => exact constant_bound bounded
  | memory signature transition => exact memory_transition_bound bounded transition

theorem Step.next_extension {before next} (step : Step before (.next next))
    (typed : CoreTyped before) : Extend_store before.store next.store := by
  cases step with
  | pure signature transition => cases transition; exact extend_store_refl _ typed.typed.store
  | constant => exact extend_store_refl _ typed.typed.store
  | memory signature transition => exact (memory_transition_preservation signature typed transition).2

theorem Step.trap_simulation {before} (step : Step before .trap) (typed : CoreTyped before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | memory signature transition => exact memory_transition_trap_simulation signature typed.typed transition

end Itasca.Runtime.Abs.Simd
