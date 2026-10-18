import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Store.Invariant.SupportedFunctionTables
import Exec.Abs.ModuleBindingsExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Store content updates retain the complete current execution certificate
when they preserve function metadata and extend the decoded specification store. -/
theorem CertifiedSupportedStore.content_update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedSupportedStore emission allowed view code before)
    (identity : after.id = before.id) (functions : after.funcs = before.funcs)
    (types : after.types = before.types) (instances : after.instances = before.instances)
    (elements : after.elems = before.elems) (data : after.datas = before.datas)
    (shape : Store.Shape view after)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)) :
    CertifiedSupportedStore emission allowed view code after := by
  have sourceSyntax : Store.StoreSyntax code after := by
    simpa only [Store.StoreSyntax, instances] using certified.storeSyntax
  have decodedFunctions : (Store.decodeStore view code after).FUNCS =
      (Store.decodeStore view code before).FUNCS := by
    have decodeFunction : Store.decodeFunction code after = Store.decodeFunction code before := by
      funext function
      simp only [Store.decodeFunction, Store.decodeInstance, types, instances]
    simp only [Store.decodeStore, functions, decodeFunction]
  refine ⟨shape, sourceSyntax, Store.core_functions_typed_metadata functions types instances extension certified.typed, ?_,
    Store.supported_compiled_functions_metadata code identity functions types instances certified.compiled, ?_⟩
  · exact certified.supported.same decodedFunctions
  · exact ⟨by simpa only [elements] using certified.segmentBounds.elements,
      by simpa only [data] using certified.segmentBounds.data⟩
end Exec.Theorems
