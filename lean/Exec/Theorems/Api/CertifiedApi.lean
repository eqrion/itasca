import Exec.Theorems.Composition.Certified.CertifiedSupportedContent
import Exec.Theorems.Composition.Certified.CertifiedSupportedCode
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Api.SupportedApiHost
import Exec.Store.Api.ExportBounds
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Public API invariant. Export descriptors retain namespace bounds in
addition to the static execution certificate; no execution conclusion is a field. -/
structure CertifiedApiStore (emission : Interp.StructuredMachine.FunctionEmission)
    (allowed : instr → Prop) {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedSupportedStore emission allowed view code store where
  exportBounds : Store.ExportBounds store

abbrev CertifiedExecutableApiStore {M : Type} :=
  @CertifiedApiStore Interp.Executable.emission Abs.ExecutableInstr M

variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem CertifiedApiStore.content_update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore emission allowed view code before)
    (identity : after.id = before.id) (functions : after.funcs = before.funcs)
    (types : after.types = before.types) (instances : after.instances = before.instances)
    (elements : after.elems = before.elems) (data : after.datas = before.datas)
    (shape : Store.Shape view after)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)) :
    CertifiedApiStore emission allowed view code after :=
  ⟨certified.toCertifiedSupportedStore.content_update identity functions types instances elements data shape extension,
    certified.exportBounds.instances_eq instances⟩

theorem CertifiedApiStore.update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore emission allowed view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedApiStore emission allowed view code after :=
  ⟨certified.toCertifiedSupportedStore.update mutation,
    certified.exportBounds.instances_eq mutation.metadata.instances⟩

theorem CertifiedApiStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore emission allowed view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedApiStore emission allowed view after store :=
  ⟨certified.toCertifiedSupportedStore.change_code agrees,certified.exportBounds⟩

theorem CertifiedApiStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore emission allowed view code store) (sources : List funccode) :
    CertifiedApiStore emission allowed view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.installCode_agrees store code sources)

theorem CertifiedApiStore.host_definition {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore emission allowed view code before)
    (shape : Store.Shape view after) (effect : Store.HostDefinitionEffect before after) :
    CertifiedApiStore emission allowed view code after ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  have post := certified.toCertifiedSupportedStore.host_definition shape effect
  exact ⟨⟨post.1,certified.exportBounds.instances_eq effect.instances⟩,post.2⟩
end Exec.Theorems
