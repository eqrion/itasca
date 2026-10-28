import Exec.Contracts
import Exec.Theorems.Composition.Eventful.EventfulWorld
import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
import Exec.Interp.Relations.StepRecording
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

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

/-- A completed dispatch either constructs its next current-code world or
retains the error's exact returned interpretation, effects and resource cause. -/
def WorldStepResult {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (before : EventfulWorld M P view expected) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ next : EventfulWorld M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulWorldTransition memory hooks floats allocator before
        (stepHostEvents before.machine.exec before.machine.store out) next
  | .Err error => ∃ afterCode,
      Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧
      FrameStorePrefix before.machine.store out.2.2.1 ∧
      Store.CodeAgreesOn before.machine.store before.code afterCode ∧
      Extend_store (Store.decodeStore view before.code before.machine.store) (Store.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (Abs.decode before.machine.source)
        (stepHostEvents before.machine.exec before.machine.store out)
        (Store.decodeStore view afterCode out.2.2.1) before.machine.source.ambient error ∧
      EventfulDispatchCause memory hooks floats allocator before.machine out error

/-- The concrete dispatcher must discharge this interface; it is not an
assumption of a final public theorem. -/
def WorldStepOutcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (expected : List valtype)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ before : EventfulWorld M P view expected,
    Inv before.code before.machine.store → 0<before.machine.exec.frames.length →
    DivSpec (HostDiverges hooks before.machine.store)
      (runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform)
      fun out => WorldStepResult memory hooks floats allocator Inv before out

theorem world_recorded_history {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n before events after) :
    Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after := by
  induction history with
  | refl state => exact .refl state
  | cons edge tail ih => exact .cons edge.edge ih

theorem EventfulWorld.history_ambient {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    after.machine.source.ambient=before.machine.source.ambient := by
  induction history with
  | refl state => rfl
  | cons edge tail ih => exact ih.trans edge.ambient
end Itasca.Runtime.Theorems
