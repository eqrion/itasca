import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeMutationCertified
import Itasca.Runtime.Interp.StructuredMachine.CompiledFunctions
import Itasca.Runtime.Abs.SupportedState
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std

/-- Common static store certificate indexed by source syntax and concrete
function emission. Execution semantics remain separate checked theorems. -/
structure CertifiedSupportedStore
 {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Interp.CoreFunctionsTyped view code store
  supported : Abs.FunctionsSupported (Store.decodeStore view code store)
  compiled : Interp.StructuredMachine.CompiledFunctions code store
  segmentBounds : Store.SegmentBounds store

theorem CertifiedSupportedStore.functions_typed {M view code store}
    (certified : @CertifiedSupportedStore M view code store) :
    Abs.FunctionsTyped (Store.decodeStore view code store) := certified.typed.functions_typed

theorem CertifiedSupportedStore.contents_typed {M view code store}
    (certified : @CertifiedSupportedStore M view code store) :
    Abs.StoreContentsTyped (Store.decodeStore view code store) :=
  Store.decodeStore_contents_typed view code store certified.shape certified.storeSyntax certified.segmentBounds

/-- Exact checked mutation footprints preserve the common static certificate,
including operations that drop segments or grow mutable objects. -/
theorem CertifiedSupportedStore.update {M view code before after}
    (certified : @CertifiedSupportedStore M view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedSupportedStore view code after := by
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

end Itasca.Runtime.Theorems
