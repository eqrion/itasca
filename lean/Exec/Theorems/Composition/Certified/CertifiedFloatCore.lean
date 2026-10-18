import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.FloatCoreState
import Exec.Interp.Machines.FloatCore.FloatCoreCompiledFunctions
import Exec.Theorems.Composition.Core.CoreContents
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Static evidence for contextual mutable scalar code. Host entries are
permitted as syntax; their execution still requires the separate host contract. -/
structure CertifiedFloatCoreStore {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Interp.CoreFunctionsTyped view code store
  core : Abs.FloatCoreFunctions (Store.decodeStore view code store)
  compiled : Interp.FloatCoreCompiledFunctions code store
  segmentBounds : Store.SegmentBounds store

theorem CertifiedFloatCoreStore.functions_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedFloatCoreStore view code store) :
    Abs.FunctionsTyped (Store.decodeStore view code store) := certified.typed.functions_typed

theorem CertifiedFloatCoreStore.contents_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedFloatCoreStore view code store) :
    Abs.StoreContentsTyped (Store.decodeStore view code store) :=
  Store.decodeStore_contents_typed view code store certified.shape certified.storeSyntax certified.segmentBounds
end Exec.Theorems
