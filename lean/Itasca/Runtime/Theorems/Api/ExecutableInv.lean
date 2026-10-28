import Itasca.Runtime.Theorems.Api.CertifiedApi
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupported
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupportedCode
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupportedSegments
import Itasca.Runtime.Interp.StructuredMachine.StatefulProjection
import Itasca.Runtime.Interp.StructuredMachine.SupportedHeadCoverage
import Itasca.Runtime.Interp.StructuredMachine.SimdPoint
import Itasca.Runtime.Interp.StructuredMachine.IndirectPoint
import Itasca.Runtime.Abs.BinaryInstr
import Itasca.Runtime.Store.Initialization.SegmentAccounting
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Invariant.TypeStaging
import Itasca.Runtime.Store.Initialization.SegmentCounts
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std

/-- Public execution invariant with the two reachable-store ledgers retained
explicitly. Host freedom is deliberately not a field. -/
structure ExecutableInv {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedExecutableApiStore view code store where
  segmentAccounting : Store.SegmentAccounting store
  capacities : Store.FunctionCapacities code store

namespace ExecutableInv

theorem well_formed {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    wf_store (Store.decodeStore view code store) :=
  Store.decodeStore_wf view code store held.shape held.storeSyntax

/-- Every store satisfying the public invariant has the generated semantic
store typing, including host functions. -/
theorem source_typed {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    Store_ok (Store.decodeStore view code store) :=
  held.toCertifiedApiStore.source_typed

theorem update {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (mutation : CumulativeStoreMutation view code before after) : ExecutableInv view code after :=
  ⟨held.toCertifiedApiStore.update mutation,
    mutation.segmentCounts.accounting mutation.metadata.instances held.segmentAccounting,
    held.capacities.metadata mutation.metadata.functions mutation.metadata.instances mutation.metadata.types mutation.metadata.identity⟩

end ExecutableInv
end Itasca.Runtime.Theorems
