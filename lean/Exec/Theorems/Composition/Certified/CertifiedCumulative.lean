import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.CumulativeState
import Exec.Interp.Machines.Cumulative.CumulativeCompiledFunctions
import Exec.Theorems.Composition.Core.CoreContents
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Static evidence for contextual mutable scalar code. Host entries are
permitted as syntax; their execution still requires the separate host contract. -/
structure CertifiedCumulativeStore {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Interp.CoreFunctionsTyped view code store
  core : Abs.CumulativeFunctions (Store.decodeStore view code store)
  compiled : Interp.CumulativeCompiledFunctions code store
  segmentBounds : Store.SegmentBounds store

theorem CertifiedCumulativeStore.functions_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code store) :
    Abs.FunctionsTyped (Store.decodeStore view code store) := certified.typed.functions_typed

theorem CertifiedCumulativeStore.contents_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code store) :
    Abs.StoreContentsTyped (Store.decodeStore view code store) :=
  Store.decodeStore_contents_typed view code store certified.shape certified.storeSyntax certified.segmentBounds
end Exec.Theorems
