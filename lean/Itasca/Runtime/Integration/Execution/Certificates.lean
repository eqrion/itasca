import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Definitions

/-!
# Internal execution certificates

Certified machines and histories construct the public source-level resource
explanation. They retain compiled-frame correspondence and administrative
progress solely for the simulation proof, not as public resource assumptions.
-/

/-! ## Integration / Execution / DispatchResult -/

section IntegrationExecutionDispatchResult

/-!
### Event-bearing dispatch result

`EventfulDispatchResult` retains the source/machine outcome and actual events for an
interpreter dispatch.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt

abbrev EventfulDispatchResult (M P : Type) :=
  core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P

end Itasca.Integration

end IntegrationExecutionDispatchResult


/-! ## Integration / Execution / OwnershipBounds -/

section IntegrationExecutionOwnershipBounds

/-!
### Source ownership bounds

`ownershipBounds` extracts the source address bounds used when relating publication to
value/frame ownership.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- The two reference namespaces are measured independently. -/
def ownershipBounds {M : Type} (store : runtime.store.Store M) : SourceMachine.Ownership.Bounds :=
  ⟨store.funcs.length,store.externs.length⟩

end Itasca.Store

end IntegrationExecutionOwnershipBounds


/-! ## Integration / Execution / Machine -/

section IntegrationExecutionMachine

/-!
### Event-bearing machine state

`EventfulMachine` retains a concrete/source machine point and the event-bearing history
used by evolving-world execution.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- An execution state with a current certificate and reference ownership.
Host callbacks may extend the store, so neither host-freedom nor a fixed bound
on the initial source store is a field of this carrier. -/
structure EventfulMachine
    (M P : Type) (view : M → Slice U8) (code : Representation.CodeInterpretation) (expected : List valtype) where
  store : runtime.store.Store M
  exec : runtime.interp.Execution
  platform : P
  source : SourceMachine.AState
  pc : Nat
  pending : Bool
  invariant : Machine.Execution view code store exec source expected pc pending
  certified : CertifiedSupportedStore view code store
  owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source

end Itasca.Integration

end IntegrationExecutionMachine

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- Internal specialization to the certified state used by dispatch proofs. -/
def EventfulSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    (machine : EventfulMachine M P view code expected)
    (out : EventfulDispatchResult M P) : runtime.ExecError → Prop :=
  DispatchResourceCause hooks allocator machine.source machine.store machine.platform out.2.2.1 out.2.2.2

end Itasca.Integration

/-! ## Integration / Execution / World -/

section IntegrationExecutionWorld

/-!
### Evolving code worlds and recorded transitions

Worlds retain current code interpretations and certified machines. Transitions connect actual dispatches, source reductions and independently recorded host events across publication.
-/

section

/-!
## Evolving code worlds

`EventfulWorld` and its transitions retain current code interpretations, executable
stores and recorded source/machine histories.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- The current source interpretation is ghost state. In particular it need
not assign the eventual source bodies of future reentrant publications. -/
structure EventfulWorld
    (M P : Type) (view : M → Slice U8) (expected : List valtype) where
  code : Representation.CodeInterpretation
  machine : EventfulMachine M P view code expected

/-- A cross-world edge keeps the actual dispatch and labeled source evidence.
It does not assert that host dispatch supplies such an edge: that obligation
must be discharged from a world-indexed callback theorem. -/
structure EventfulWorldTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld M P view expected) (events : List SpecExt.HostEvent)
    (after : EventfulWorld M P view expected) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.machine.exec
    before.machine.store before.machine.platform =
    .ok (.Ok (),after.machine.exec,after.machine.store,after.machine.platform)
  simulation : EventfulConcreteSim U32.max before.machine.pc after.machine.pc
    before.machine.pending after.machine.pending before.machine.source after.machine.source events
  extension : Extend_store (Representation.decodeStore view before.code before.machine.store)
    (Representation.decodeStore view after.code after.machine.store)
  metadata : Store.MetadataExtended before.machine.store after.machine.store
  ambient : after.machine.source.ambient = before.machine.source.ambient
  agrees : Store.CodeAgreesOn before.machine.store before.code after.code

end Itasca.Integration

end

section

/-!
## Recorded world transition

`WorldRecordedTransition` describes an actual recorded transition while preserving the
interpretation of retained code across publication.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- Cross-world simulation with the independent raw callsite recording. -/
structure WorldRecordedTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld M P view expected) (events : List HostEvent)
    (after : EventfulWorld M P view expected) : Prop where
  edge : EventfulWorldTransition memory hooks floats allocator before events after
  recorded : events=stepHostEvents before.machine.exec before.machine.store
    (.Ok (),after.machine.exec,after.machine.store,after.machine.platform)

end Itasca.Integration

end

end IntegrationExecutionWorld

/-! ## Integration / Execution / WorldResources -/

section IntegrationExecutionWorldResources

/-!
### World-loop resource causes

`WorldLoopResourceCause` retains resource-cause evidence through the evolving-world
interpreter loop.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- A failed dispatch retains its actual reached world and source-sized
resource request, even when earlier callbacks published new modules. -/
def WorldLoopResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected)
    (result : ExecutionResult M P) (error : runtime.ExecError) : Prop :=
  ∃ previous : EventfulWorld M P view expected, ∃ count events afterExec afterStore afterPlatform,
    Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events previous ∧
    StepsH (SourceMachine.decode initial.machine.source) events (SourceMachine.decode previous.machine.source) ∧
    Inv previous.code previous.machine.store ∧
    runtime.interp.step memory hooks floats allocator previous.machine.exec previous.machine.store previous.machine.platform=
      .ok (.Err error,afterExec,afterStore,afterPlatform) ∧
    EventfulSourceResourceCause hooks allocator previous.machine (.Err error,afterExec,afterStore,afterPlatform) error ∧
    finishExecution (afterExec,afterStore,afterPlatform,.Err error)=result

end Itasca.Integration

end IntegrationExecutionWorldResources
