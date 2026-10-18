import Exec.Theorems.Api.NewCertifiedApi
import Exec.Store.Initialization.SegmentCounts
namespace Exec.Theorems
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

theorem content_update {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (identity : after.id = before.id) (functions : after.funcs = before.funcs)
    (types : after.types = before.types) (instances : after.instances = before.instances)
    (elements : after.elems = before.elems) (data : after.datas = before.datas)
    (shape : Store.Shape view after)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)) :
    ExecutableInv view code after :=
  ⟨held.toCertifiedApiStore.content_update identity functions types instances elements data shape extension,
    held.segmentAccounting.preserve elements data instances,
    held.capacities.metadata functions instances types identity⟩

theorem update {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (mutation : CumulativeStoreMutation view code before after) : ExecutableInv view code after :=
  ⟨held.toCertifiedApiStore.update mutation,
    mutation.segmentCounts.accounting mutation.metadata.instances held.segmentAccounting,
    held.capacities.metadata mutation.metadata.functions mutation.metadata.instances mutation.metadata.types mutation.metadata.identity⟩

theorem host_definition {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (shape : Store.Shape view after) (effect : Store.HostDefinitionEffect before after)
    (capacities : Store.FunctionCapacities code after) :
    ExecutableInv view code after ∧ Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  have fresh := held.toCertifiedApiStore.host_definition shape effect
  exact ⟨⟨fresh.1,held.segmentAccounting.preserve effect.elements effect.datas effect.instances,capacities⟩,fresh.2⟩

theorem new {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store => ExecutableInv view code store ⦄ := by
  apply WP.spec_mono (new_certified_executable_api memory view code id limits identity)
  rintro store ⟨certified,accounted,capacities⟩
  exact ⟨certified,accounted,capacities⟩
end ExecutableInv
end Exec.Theorems
