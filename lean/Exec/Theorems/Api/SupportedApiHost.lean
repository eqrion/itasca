import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Store.Invariant.SupportedFunctionTables
import Exec.Store.Api.DefineHostEffect
import Exec.Store.Api.DefineHost
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.CapacityHost
namespace Exec.Theorems
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Publishing host metadata extends the static executable certificate. This
lemma asserts no behavioral property of the eventual host callback. -/
theorem CertifiedSupportedStore.host_definition {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedSupportedStore emission allowed view code before)
    (shape : Store.Shape view after) (effect : Store.HostDefinitionEffect before after) :
    CertifiedSupportedStore emission allowed view code after ∧
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
/-- The public host-definition operation preserves the complete static store
certificate and canonical frame-capacity ledger on success and rejection. -/
theorem define_host_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator store ty identity ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result,returned,shape⟩ := WP.spec_imp_exists
    (Store.define_host_preserves_shape memory allocator allocation view store certified.shape ty identity)
  have effect := Store.define_host_effect memory allocator allocation store bound ty identity
  have ledger := Store.define_host_capacities memory allocator allocation view store certified.shape code capacities ty identity
  rw [returned,WP.spec_ok] at effect ledger ⊢
  have fresh := certified.host_definition shape effect
  exact ⟨fresh.1,ledger,fresh.2⟩
end SupportedApi
end Exec.Theorems
