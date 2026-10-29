import Itasca.Runtime.Integration.Execution.Ownership.CertifiedStore
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
namespace Itasca.Runtime.Integration
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
  · rw [Store.decode_store_code_agrees view agrees]
    exact certified.supported
  case compiled =>
    intro function present instanceIndex functionIndex defined
    obtain ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,source,table,types,certificate⟩ :=
      certified.compiled function present instanceIndex functionIndex defined
    exact ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,
      (agrees instanceIndex.val inst found functionIndex.val).trans source,table,types,certificate⟩

end Itasca.Runtime.Integration
