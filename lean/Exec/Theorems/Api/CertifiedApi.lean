import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Store.Invariant.SupportedFunctionTables
import Exec.Abs.ModuleBindingsExtension
import Exec.Theorems.Composition.Certified.CertifiedSupportedCode
import Exec.Theorems.Composition.Certified.CertifiedSupportedSegments
import Exec.Interp.StructuredMachine.StatefulProjection
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.SimdPoint
import Exec.Interp.StructuredMachine.IndirectPoint
import Exec.Abs.BinaryInstr
import Exec.Store.Invariant.TypeStaging
import Exec.Store.Invariant.InternTypes
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Api.ExportBounds
import Exec.Store.Invariant.SourceStoreTyping
namespace Exec.Theorems
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

end Exec.Theorems
