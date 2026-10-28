import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupported
import Itasca.Runtime.Store.Invariant.SupportedFunctionTables
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupportedCode
import Itasca.Runtime.Theorems.Composition.Certified.CertifiedSupportedSegments
import Itasca.Runtime.Interp.StructuredMachine.StatefulProjection
import Itasca.Runtime.Interp.StructuredMachine.SupportedHeadCoverage
import Itasca.Runtime.Interp.StructuredMachine.SimdPoint
import Itasca.Runtime.Interp.StructuredMachine.IndirectPoint
import Itasca.Runtime.Abs.BinaryInstr
import Itasca.Runtime.Store.Invariant.TypeStaging
import Itasca.Runtime.Store.Invariant.InternTypes
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Api.ExportBounds
import Itasca.Runtime.Store.Invariant.SourceStoreTyping
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std

/-- Public API invariant. Export descriptors retain namespace bounds in
addition to the static execution certificate; no execution conclusion is a field. -/
structure CertifiedApiStore
 {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedSupportedStore view code store where
  exportBounds : Store.ExportBounds store

abbrev CertifiedExecutableApiStore {M : Type} :=
  @CertifiedApiStore M

/-- The retained component, body, module-map and export certificates imply
full generated source store typing; it is not an invariant field. -/
theorem CertifiedApiStore.source_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) :
    Store_ok (Store.decodeStore view code store) :=
  Store.decodeStore_typed view code store certified.shape certified.storeSyntax
    certified.typed certified.segmentBounds certified.exportBounds

theorem CertifiedApiStore.update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedApiStore view code after :=
  ⟨certified.toCertifiedSupportedStore.update mutation,
    certified.exportBounds.instances_eq mutation.metadata.instances⟩

theorem CertifiedApiStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedApiStore view after store :=
  ⟨certified.toCertifiedSupportedStore.change_code agrees,certified.exportBounds⟩

theorem CertifiedApiStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) (sources : List funccode) :
    CertifiedApiStore view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.installCode_agrees store code sources)

end Itasca.Runtime.Theorems
