import Exec.Theorems.Composition.Certified.CertifiedCumulative
import Exec.Store.Invariant.CumulativeCodeAgreement
import Exec.Store.Invariant.CoreTypingExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Reassigning ghost source code at unused instance keys preserves the full
static store certificate. Actual installed functions keep their exact source. -/
theorem CertifiedCumulativeStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedCumulativeStore view after store := by
  refine ⟨certified.shape, ?_, ?_, ?_, Store.cumulative_compiled_functions_code_agrees agrees certified.compiled, certified.segmentBounds⟩
  · intro index inst found
    have priorSyntax := certified.storeSyntax index inst found
    refine ⟨priorSyntax.exportNames, ?_⟩
    intro function bound
    rw [agrees index inst found function]
    exact priorSyntax.functionCodes function bound
  · exact Store.core_functions_typed_code_agrees agrees certified.typed
  · rw [Store.decodeStore_code_agrees view agrees]
    exact certified.core

/-- The source assignment used to publish a fresh instance can already be
installed on the unchanged old store, including after precommit rollback. -/
theorem CertifiedCumulativeStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code store) (sources : List funccode) :
    CertifiedCumulativeStore view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.installCode_agrees store code sources)
end Exec.Theorems
