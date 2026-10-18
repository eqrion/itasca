import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Store.Invariant.CumulativeCodeAgreement
import Exec.Store.Invariant.CoreTypingExtension
namespace Exec.Theorems
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}
open Aeneas Aeneas.Std

/-- Reassigning ghost source code at unused instance keys preserves the full
static store certificate. Actual installed functions keep their exact source. -/
theorem CertifiedSupportedStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSupportedStore emission allowed view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedSupportedStore emission allowed view after store := by
  refine ⟨certified.shape, ?_, ?_, ?_, ?compiled, certified.segmentBounds⟩
  · intro index inst found
    have priorSyntax := certified.storeSyntax index inst found
    refine ⟨priorSyntax.exportNames, ?_⟩
    intro function bound
    rw [agrees index inst found function]
    exact priorSyntax.functionCodes function bound
  · exact Store.core_functions_typed_code_agrees agrees certified.typed
  · rw [Store.decodeStore_code_agrees view agrees]
    exact certified.supported
  case compiled =>
    intro function present instanceIndex functionIndex defined
    obtain ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,source,table,types,certificate⟩ :=
      certified.compiled function present instanceIndex functionIndex defined
    exact ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,
      (agrees instanceIndex.val inst found functionIndex.val).trans source,table,types,certificate⟩

/-- The source assignment used to publish a fresh instance can already be
installed on the unchanged old store, including after precommit rollback. -/
theorem CertifiedSupportedStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSupportedStore emission allowed view code store) (sources : List funccode) :
    CertifiedSupportedStore emission allowed view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.installCode_agrees store code sources)
end Exec.Theorems
