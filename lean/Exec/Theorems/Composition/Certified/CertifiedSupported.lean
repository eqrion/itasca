import Exec.Theorems.Composition.Cumulative.CumulativeMutationCertified
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Abs.SupportedState
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Common static store certificate indexed by source syntax and concrete
function emission. Execution semantics remain separate checked theorems. -/
structure CertifiedSupportedStore (emission : Interp.StructuredMachine.FunctionEmission)
    (allowed : instr → Prop) {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Interp.CoreFunctionsTyped view code store
  supported : Abs.FunctionsSupported allowed (Store.decodeStore view code store)
  compiled : Interp.StructuredMachine.CompiledFunctions emission code store
  segmentBounds : Store.SegmentBounds store

theorem CertifiedSupportedStore.functions_typed {emission allowed M view code store}
    (certified : @CertifiedSupportedStore emission allowed M view code store) :
    Abs.FunctionsTyped (Store.decodeStore view code store) := certified.typed.functions_typed

theorem CertifiedSupportedStore.contents_typed {emission allowed M view code store}
    (certified : @CertifiedSupportedStore emission allowed M view code store) :
    Abs.StoreContentsTyped (Store.decodeStore view code store) :=
  Store.decodeStore_contents_typed view code store certified.shape certified.storeSyntax certified.segmentBounds

/-- Exact checked mutation footprints preserve the common static certificate,
including operations that drop segments or grow mutable objects. -/
theorem CertifiedSupportedStore.update {emission allowed M view code before after}
    (certified : @CertifiedSupportedStore emission allowed M view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedSupportedStore emission allowed view code after := by
  have syntaxAfter : Store.StoreSyntax code after := by
    simpa only [Store.StoreSyntax,mutation.metadata.instances] using certified.storeSyntax
  have decodedFunctions : (Store.decodeStore view code after).FUNCS =
      (Store.decodeStore view code before).FUNCS := by
    have decodeFunction : Store.decodeFunction code after = Store.decodeFunction code before := by
      funext function
      simp only [Store.decodeFunction,Store.decodeInstance,mutation.metadata.types,mutation.metadata.instances]
    simp only [Store.decodeStore,mutation.metadata.functions,decodeFunction]
  refine ⟨mutation.shape,syntaxAfter,
    Store.core_functions_typed_metadata mutation.metadata.functions mutation.metadata.types mutation.metadata.instances
      mutation.extension certified.typed,certified.supported.same decodedFunctions,?_,mutation.segmentBounds⟩
  simpa only [Interp.StructuredMachine.CompiledFunctions,Interp.StructuredMachine.FunctionCompiled,Interp.FunctionTable,
    Store.decodeInstance,mutation.metadata.identity,mutation.metadata.functions,mutation.metadata.types,
    mutation.metadata.instances] using certified.compiled

theorem CertifiedSupportedStore.mutation_refl {emission allowed M view code store}
    (certified : @CertifiedSupportedStore emission allowed M view code store) :
    CumulativeStoreMutation view code store store :=
  ⟨.refl store,rfl,certified.shape,certified.segmentBounds,
    Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),.refl store,rfl⟩
end Exec.Theorems
