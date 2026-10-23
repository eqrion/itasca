import Exec.Theorems.Composition.Eventful.EventfulWorldStep
import Exec.Theorems.Composition.Cumulative.CumulativeNormalizeOutcome
import Exec.Interp.Relations.EventfulNormalize
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Unbundled source-indexed form of the world result, used while erased
source normalization changes the source point without executing a raw step. -/
def WorldSourceStepResult {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Store.CodeInterpretation) (expected : List valtype)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (pc : Nat) (pending : Bool) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ next : EventfulWorld M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulConcreteSim U32.max pc next.machine.pc pending next.machine.pending source next.machine.source
        (stepHostEvents exec store out) ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view next.code next.machine.store) ∧
      FrameStorePrefix store next.machine.store ∧ next.machine.source.ambient=source.ambient ∧
      Store.CodeAgreesOn store code next.code
  | .Err error => ∃ afterCode,
      Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧
      FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (Abs.decode source) (stepHostEvents exec store out)
        (Store.decodeStore view afterCode out.2.2.1) source.ambient error ∧
      ((CumulativeFailure allocator hooks exec store platform source error ∧
        Store.decodeStore view code out.2.2.1=source.store) ∨
       HostDispatchCause memory hooks floats allocator exec store platform source out error)

theorem WorldStepResult.unbundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld M P view expected} {out : EventfulDispatchResult M P}
    (result : WorldStepResult memory hooks floats allocator Inv before out) :
    WorldSourceStepResult (view:=view) memory hooks floats allocator Inv before.code expected before.machine.exec
      before.machine.store before.machine.platform before.machine.source before.machine.pc before.machine.pending out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,edge⟩ := result
    exact ⟨next,valid,equal,edge.simulation,edge.extension,edge.metadata,edge.ambient,edge.agrees⟩
  | Err error => simpa only [WorldStepResult,WorldSourceStepResult,status,EventfulDispatchCause] using result

theorem WorldSourceStepResult.bundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld M P view expected} {out : EventfulDispatchResult M P}
    (result : WorldSourceStepResult (view:=view) memory hooks floats allocator Inv before.code expected before.machine.exec
      before.machine.store before.machine.platform before.machine.source before.machine.pc before.machine.pending out)
    (actual : runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store
      before.machine.platform=.ok out) : WorldStepResult memory hooks floats allocator Inv before out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambient,agrees⟩ := result
    exact ⟨next,valid,equal,actual.trans (congrArg Result.ok equal),simulation,extension,retained,ambient,agrees⟩
  | Err error => simpa only [WorldStepResult,WorldSourceStepResult,status,EventfulDispatchCause] using result

theorem WorldSourceStepResult.prepend_normalization {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {count pc : Nat} {s : _root_.store} {ambient : frame} {before middle : Abs.AFrame} {rest : List Abs.AFrame}
    {out : EventfulDispatchResult M P}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (result : WorldSourceStepResult (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,middle::rest,[]⟩ pc false out) :
    WorldSourceStepResult (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,before::rest,[]⟩ pc false out := by
  have normalized := chain.sound s ambient rest typed
  have prefixSteps : StepsH (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,middle::rest,[]⟩) := by
    rcases normalized.2 with ⟨rank,same⟩ | simulation
    · simpa only [same] using StepsH.refl typed.decode_wf
    · rcases simulation with ⟨same,decrease⟩ | ⟨n,positive,steps⟩
      · rw [same]
        exact StepsH.refl normalized.1.decode_wf
      · exact steps.erase
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambientEq,agrees⟩ := result
    exact ⟨next,valid,equal,simulation.prepend_normalization chain s ambient rest typed,extension,retained,ambientEq,agrees⟩
  | Err error =>
    simp only [WorldSourceStepResult,status] at result ⊢
    obtain ⟨afterCode,valid,certified,retained,agrees,extension,outcome,cause⟩ := result
    refine ⟨afterCode,valid,certified,retained,agrees,extension,?_,?_⟩
    · simpa only [List.nil_append] using outcome.prepend prefixSteps
    · rcases cause with ⟨failure,decoded⟩ | host
      · exact Or.inl ⟨failure.prepend_normalization chain typed,decoded⟩
      · exact Or.inr (host.prepend prefixSteps rfl rfl)
end Exec.Theorems
