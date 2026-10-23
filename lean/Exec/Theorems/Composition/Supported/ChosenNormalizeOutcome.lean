import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Interp.Relations.ChosenConcretePrefix
import Exec.Interp.Relations.ErasedChosen
import Exec.Theorems.Composition.Supported.SupportedNormalizeOutcome
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

theorem StructuredMachine.ChosenAdvance.prepend_normalization
    {choices : SourceChoices} {occurrence prefixCount : Nat}
 {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (source : ChosenStepsN choices occurrence prefixCount (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,middle::rest,[]⟩))
    (bounded : prefixCount=0 → Abs.administrativeMeasure ⟨s,ambient,middle::rest,[]⟩ ≤ Abs.administrativeMeasure ⟨s,ambient,before::rest,[]⟩)
    (advance : StructuredMachine.ChosenAdvance choices (occurrence+prefixCount) view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    StructuredMachine.ChosenAdvance choices occurrence view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambientEq,codeBound⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend source bounded,
    fun bound owned=>ownership bound (chain.ownership.stateful owned),ambientEq,fun bound h=>codeBound bound (chain.codeBound h)⟩

theorem ChosenCumulativeFailure.prepend_normalization
    {choices : SourceChoices} (admissible : choices.Admissible) {occurrence prefixCount : Nat}
    {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (source : ChosenStepsN choices occurrence prefixCount (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,middle::rest,[]⟩))
    (failure : ChosenCumulativeFailure choices (occurrence+prefixCount) allocator hooks exec store platform ⟨s,ambient,middle::rest,[]⟩ error) :
    ChosenCumulativeFailure choices occurrence allocator hooks exec store platform ⟨s,ambient,before::rest,[]⟩ error := by
  rcases failure with ⟨kind,n,positive,steps⟩ | interrupted | rejected
  · exact .inl ⟨kind,prefixCount+n,by omega,by simpa only [List.nil_append] using source.trans steps⟩
  · exact .inr (.inl interrupted)
  · obtain ⟨index,raw,inst,compiled,last,frameFound,instanceFound,codeFound,cause⟩ := rejected
    refine .inr (.inr ⟨index,raw,inst,compiled,last,frameFound,instanceFound,codeFound,?_⟩)
    rcases cause with direct | ⟨code,indirect⟩
    · exact .inl (direct.prepend (source.erases admissible) rfl rfl)
    · exact .inr ⟨code,indirect.prepend (source.erases admissible) rfl rfl⟩

theorem ChosenSupportedStepOutcome.prepend_normalization
    {choices : SourceChoices} (admissible : choices.Admissible) {occurrence prefixCount : Nat}
 {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (source : ChosenStepsN choices occurrence prefixCount (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,middle::rest,[]⟩))
    (bounded : prefixCount=0 → Abs.administrativeMeasure ⟨s,ambient,middle::rest,[]⟩ ≤ Abs.administrativeMeasure ⟨s,ambient,before::rest,[]⟩)
    (outcome : ChosenSupportedStepOutcome choices (occurrence+prefixCount) allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
  obtain ⟨mutation,transition⟩ := outcome
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact StructuredMachine.ChosenAdvance.prepend_normalization chain source bounded transition
  | Err error =>
    simp only [status] at transition ⊢
    exact ⟨transition.1.prepend_normalization admissible chain source,transition.2⟩
end Exec.Theorems
