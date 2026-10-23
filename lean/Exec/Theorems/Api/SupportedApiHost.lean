import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Store.Invariant.SupportedFunctionTables
import Exec.Store.Api.DefineHostEffect
import Exec.Store.Api.DefineHost
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.CapacityHost
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Publishing host metadata extends the static executable certificate. This
lemma asserts no behavioral property of the eventual host callback. -/
theorem CertifiedSupportedStore.host_definition {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedSupportedStore view code before)
    (shape : Store.Shape view after) (effect : Store.HostDefinitionEffect before after) :
    CertifiedSupportedStore view code after ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  have sourceSyntax : Store.StoreSyntax code after := by
    simpa only [Store.StoreSyntax,effect.instances] using certified.storeSyntax
  have extension := Store.staged_extends view code before after certified.shape shape
    certified.storeSyntax sourceSyntax effect.retained
  refine ⟨⟨shape,sourceSyntax,?_,?_,?_,?_⟩,extension⟩
  · intro fn present
    rcases effect.functions fn present with old | ⟨identity,host⟩
    · exact Store.core_function_typed_prefix view code before after certified.shape effect.retained extension
        fn old (certified.typed fn old)
    · simp only [Interp.CoreFunctionTyped,host]
      generalize (Store.decodeFunction code after fn).TYPE = ft
      rcases ft with ⟨⟨params⟩,⟨results⟩⟩
      constructor
  · intro fn present
    obtain ⟨raw,member,rfl⟩ := List.mem_map.mp present
    rcases effect.functions raw member with old | ⟨identity,host⟩
    · rw [Store.decodeFunction_prefix code before after effect.retained view certified.shape raw old]
      exact certified.supported _ (List.mem_map.mpr ⟨raw,old,rfl⟩)
    · simp [Store.decodeFunction,host]
  · intro fn present
    rcases effect.functions fn present with old | ⟨identity,host⟩
    · exact Store.supported_function_compiled_prefix certified.shape effect.retained
        (fun _ _ _ _ => rfl) (certified.compiled fn old)
    · intro ii fi impossible
      rw [host] at impossible
      cases impossible
  · exact ⟨by simpa only [effect.elements] using certified.segmentBounds.elements,
      by simpa only [effect.datas] using certified.segmentBounds.data⟩

namespace SupportedApi
end SupportedApi
end Exec.Theorems
