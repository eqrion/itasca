import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Spec.Steps
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Resource witnesses discovered during a start call remain reachable after
prepending the already checked source resolution or initialization steps. -/
theorem InvocationBoundaryCause.prepend {M P : Type} {hooks : runtime.platform.Platform P M}
    {initial next : config} {limit : Nat} {error : runtime.ExecError}
    (cause : InvocationBoundaryCause hooks next limit error) (prefixSteps : StepsH initial [] next) :
    InvocationBoundaryCause hooks initial limit error := by
  cases error with
  | Exhausted limitKind =>
    cases limitKind <;> simp only [InvocationBoundaryCause] at cause ⊢
    all_goals try trivial
    rcases cause with exceeded | ⟨final,steps,exceeded⟩
    · exact Or.inr ⟨next,prefixSteps,exceeded⟩
    · exact Or.inr ⟨final,by simpa using Spec.stepsH_trans prefixSteps steps,exceeded⟩
  | Terminated => exact cause
  | _ => trivial

theorem CanonicalInvocationResourceCause.prepend {A M P : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {initial next : config} {store : _root_.store} {signature : functype} {address : funcaddr}
    {valueLimit frameLimit : Nat} {error : runtime.ExecError}
    (cause : CanonicalInvocationResourceCause allocator hooks next store signature address valueLimit frameLimit error)
    (prefixSteps : StepsH initial [] next) :
    CanonicalInvocationResourceCause allocator hooks initial store signature address valueLimit frameLimit error := by
  cases error with
  | Exhausted limitKind =>
    cases limitKind with
    | Values =>
      rcases cause with signatureCause | capacityCause | ⟨source,callee,base,words,steps,site,capacity,exceeded⟩
      · exact Or.inl signatureCause
      · exact Or.inr (Or.inl capacityCause)
      · exact Or.inr (Or.inr ⟨source,callee,base,words,by simpa using Spec.stepsH_trans prefixSteps steps,site,capacity,exceeded⟩)
    | Allocation =>
      rcases cause with signatureCause | capacityCause | ⟨source,steps,refused⟩
      · exact Or.inl signatureCause
      · exact Or.inr (Or.inl capacityCause)
      · exact Or.inr (Or.inr ⟨source,by simpa using Spec.stepsH_trans prefixSteps steps,refused⟩)
    | Objects => exact cause
    | CallStack =>
      simp only [CanonicalInvocationResourceCause] at cause ⊢
      exact InvocationBoundaryCause.prepend cause prefixSteps
  | _ =>
    simp only [CanonicalInvocationResourceCause] at cause ⊢
    exact InvocationBoundaryCause.prepend cause prefixSteps
end Exec.Theorems
