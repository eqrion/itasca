import Exec.Theorems.Composition.World.WorldSourceStep
import Exec.Interp.Relations.ChosenEventfulControl
import Exec.Theorems.Composition.Eventful.ChosenEventfulErrors
import Exec.Theorems.Composition.Cumulative.CumulativeNormalizeOutcome
import Exec.Interp.Relations.EventfulNormalize
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Unbundled source-indexed form of the world result, used while erased
source normalization changes the source point without executing a raw step. -/
def ChosenWorldSourceStepResult (choices : Spec.SourceChoices) (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Store.CodeInterpretation) (expected : List valtype)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (pc : Nat) (pending : Bool) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ next : EventfulWorld emission allowed M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      ChosenEventfulConcreteSim choices occurrence U32.max pc next.machine.pc pending next.machine.pending source next.machine.source
        (stepHostEvents exec store out) ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view next.code next.machine.store) ∧
      FrameStorePrefix store next.machine.store ∧ next.machine.source.ambient=source.ambient ∧
      Store.CodeAgreesOn store code next.code
  | .Err error => ∃ afterCode,
      Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore emission allowed view afterCode out.2.2.1 ∧
      FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
      ChosenEventfulInvocationError choices occurrence (Abs.decode source) (stepHostEvents exec store out)
        (Store.decodeStore view afterCode out.2.2.1) source.ambient error ∧
      ((CumulativeFailure allocator hooks exec store platform source error ∧
        Store.decodeStore view code out.2.2.1=source.store) ∨
       HostDispatchCause memory hooks floats allocator exec store platform source out error)


theorem ChosenWorldSourceStepResult.erases {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    {M P F A memory hooks floats allocator view Inv code expected exec store platform source pc pending out occurrence}
    (result : ChosenWorldSourceStepResult choices occurrence (M:=M) (P:=P) (F:=F) (A:=A)
      (emission:=emission) (allowed:=allowed) (view:=view) memory hooks floats allocator Inv code expected exec store platform source pc pending out) :
    WorldSourceStepResult (emission:=emission) (allowed:=allowed) (view:=view) memory hooks floats allocator Inv code expected exec store platform source pc pending out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [ChosenWorldSourceStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambient,agrees⟩ := result
    exact ⟨next,valid,equal,simulation.erases admissible,extension,retained,ambient,agrees⟩
  | Err error =>
    simp only [ChosenWorldSourceStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨afterCode,valid,certified,retained,agrees,extension,outcome,cause⟩ := result
    exact ⟨afterCode,valid,certified,retained,agrees,extension,outcome.erases admissible,cause⟩

theorem ChosenWorldSourceStepResult.prepend_normalization {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    {M P F A : Type} {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {count sourceCount occurrence pc : Nat} {s : _root_.store} {ambient : frame} {before middle : Abs.AFrame} {rest : List Abs.AFrame}
    {out : EventfulDispatchResult M P}
    (chain : ErasedSteps count before middle)
    (prefixSteps : Spec.ChosenStepsN choices occurrence sourceCount (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,middle::rest,[]⟩))
    (bounded : sourceCount=0 → Abs.administrativeMeasure ⟨s,ambient,middle::rest,[]⟩≤Abs.administrativeMeasure ⟨s,ambient,before::rest,[]⟩)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (result : ChosenWorldSourceStepResult choices (occurrence+sourceCount) (emission:=emission) (allowed:=allowed) (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,middle::rest,[]⟩ pc false out) :
    ChosenWorldSourceStepResult choices occurrence (emission:=emission) (allowed:=allowed) (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,before::rest,[]⟩ pc false out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [ChosenWorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambientEq,agrees⟩ := result
    exact ⟨next,valid,equal,simulation.prepend prefixSteps bounded,extension,retained,ambientEq,agrees⟩
  | Err error =>
    simp only [ChosenWorldSourceStepResult,status] at result ⊢
    obtain ⟨afterCode,valid,certified,retained,agrees,extension,outcome,cause⟩ := result
    refine ⟨afterCode,valid,certified,retained,agrees,extension,?_,?_⟩
    · simpa only [List.nil_append] using outcome.prepend prefixSteps
    · rcases cause with ⟨failure,decoded⟩ | host
      · exact Or.inl ⟨failure.prepend_normalization chain typed,decoded⟩
      · exact Or.inr (host.prepend (prefixSteps.erases admissible).erase rfl rfl)
end Exec.Theorems
