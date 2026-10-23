import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.CoreTypingExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Reassigning ghost source code at unused instance keys preserves the full
static store certificate. Actual installed functions keep their exact source. -/
theorem CertifiedSupportedStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSupportedStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedSupportedStore view after store := by
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

end Exec.Theorems
