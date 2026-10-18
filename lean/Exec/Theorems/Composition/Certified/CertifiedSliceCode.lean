import Exec.Theorems.Composition.Certified.CertifiedSlice
import Exec.Store.Invariant.CodeAgreement
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Reassigning ghost source code at unused instance keys preserves the full
static store certificate. Actual installed functions keep their exact source. -/
theorem CertifiedSliceStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSliceStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedSliceStore view after store := by
  refine ⟨certified.shape, ?_, ?_, ?_, Store.compiled_functions_code_agrees agrees certified.compiled, certified.segmentBounds⟩
  · intro index inst found
    have priorSyntax := certified.storeSyntax index inst found
    refine ⟨priorSyntax.exportNames, ?_⟩
    intro function bound
    rw [agrees index inst found function]
    exact priorSyntax.functionCodes function bound
  · rw [Store.decodeStore_code_agrees view agrees]
    exact certified.typed
  · rw [Store.decodeStore_code_agrees view agrees]
    exact certified.slice

/-- The source assignment used to publish a fresh instance can already be
installed on the unchanged old store, including after precommit rollback. -/
theorem CertifiedSliceStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSliceStore view code store) (sources : List funccode) :
    CertifiedSliceStore view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.installCode_agrees store code sources)
end Exec.Theorems
