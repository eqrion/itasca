import Exec.Theorems.Composition.Uniform.UniformWorldHistory
import Exec.Theorems.Composition.Uniform.UniformSupportedTransport
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def UniformWorldSourceSuccess {M P : Type} {view : M → Slice U8}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Store.CodeInterpretation) (expected : List valtype)
    (store : runtime.store.Store M) (source : Abs.AState) (pc : Nat) (pending : Bool)
    (out : EventfulDispatchResult M P) : Prop :=
  out.1=.Ok () → ∃events,∃next : EventfulWorld emission allowed M P view expected,
    Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
    EventfulConcreteSim U32.max pc next.machine.pc pending next.machine.pending source next.machine.source events ∧
    UniformConcreteSim pc next.machine.pc pending next.machine.pending source next.machine.source events ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view next.code next.machine.store) ∧
    FrameStorePrefix store next.machine.store ∧ next.machine.source.ambient=source.ambient ∧
    Store.CodeAgreesOn store code next.code

theorem UniformWorldSourceSuccess.unbundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld emission allowed M P view expected} {out : EventfulDispatchResult M P}
    (result : out.1=.Ok () → ∃next : EventfulWorld emission allowed M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      UniformWorldTransition memory hooks floats allocator before
        (stepHostEvents before.machine.exec before.machine.store out) next) :
    UniformWorldSourceSuccess (emission:=emission) (allowed:=allowed) (view:=view) Inv before.code expected before.machine.store before.machine.source before.machine.pc before.machine.pending out := by
  intro success
  obtain ⟨next,valid,equal,edge⟩ := result success
  exact ⟨_,next,valid,equal,edge.simulation,edge.uniform,edge.extension,edge.metadata,edge.ambient,edge.agrees⟩

theorem UniformWorldSourceSuccess.bundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld emission allowed M P view expected} {out : EventfulDispatchResult M P}
    (result : UniformWorldSourceSuccess (emission:=emission) (allowed:=allowed) (view:=view) Inv before.code expected before.machine.store before.machine.source before.machine.pc before.machine.pending out)
    (actual : runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform=.ok out) :
    out.1=.Ok () → ∃events,∃next : EventfulWorld emission allowed M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      UniformWorldTransition memory hooks floats allocator before events next := by
  intro success
  obtain ⟨events,next,valid,equal,simulation,uniform,extension,metadata,ambient,agrees⟩ := result success
  exact ⟨events,next,valid,equal,⟨actual.trans (congrArg Result.ok equal),simulation,extension,metadata,ambient,agrees⟩,uniform⟩

theorem UniformWorldSourceSuccess.prepend_normalization {M P : Type} {view : M → Slice U8}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {code : Store.CodeInterpretation} {expected : List valtype} {store : runtime.store.Store M}
    {s : _root_.store} {ambient : frame} {before middle : Abs.AFrame} {rest : List Abs.AFrame} {count pc : Nat}
    {out : EventfulDispatchResult M P}
    (result : UniformWorldSourceSuccess (emission:=emission) (allowed:=allowed) (view:=view) Inv code expected store
      ⟨s,ambient,middle::rest,[]⟩ pc false out)
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩) :
    UniformWorldSourceSuccess (emission:=emission) (allowed:=allowed) (view:=view) Inv code expected store
      ⟨s,ambient,before::rest,[]⟩ pc false out := by
  intro success
  obtain ⟨events,next,valid,equal,simulation,uniform,extension,metadata,ambientEq,agrees⟩ := result success
  exact ⟨events,next,valid,equal,simulation.prepend_normalization chain s ambient rest typed,
    uniform.prepend_normalization chain s ambient rest typed,extension,metadata,ambientEq,agrees⟩
end Exec.Theorems
