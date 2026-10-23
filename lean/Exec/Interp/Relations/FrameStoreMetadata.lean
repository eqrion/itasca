import Exec.Interp.Relations.StackRelation

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Runtime content mutations preserve the metadata used by every active or
suspended compiled frame. Object payloads and resource counters may change. -/
structure FrameStoreMetadata {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs = before.funcs
  types : after.types = before.types
  instances : after.instances = before.instances

theorem FrameStoreMetadata.refl {M : Type} (store : runtime.store.Store M) :
    FrameStoreMetadata store store := ⟨rfl,rfl,rfl,rfl⟩
theorem FrameStoreMetadata.trans {M : Type} {a b c : runtime.store.Store M}
    (first : FrameStoreMetadata a b) (second : FrameStoreMetadata b c) : FrameStoreMetadata a c :=
  ⟨second.identity.trans first.identity,second.functions.trans first.functions,
    second.types.trans first.types,second.instances.trans first.instances⟩

theorem FrameStoreMetadata.decodeInstance {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) (inst : runtime.store.ModuleInst) :
    Store.decodeInstance after inst = Store.decodeInstance before inst := by
  simp only [Store.decodeInstance, metadata.types]

theorem FunctionTable.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {inst functions}
    (table : FunctionTable before inst functions) : FunctionTable after inst functions := by
  simpa only [FunctionTable, metadata.identity, metadata.functions, metadata.types] using table

theorem FrameBinding.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec raw source}
    (binding : FrameBinding before exec raw source) : FrameBinding after exec raw source := by
  simpa only [FrameBinding, metadata.identity, metadata.functions, metadata.types,
    metadata.instances, metadata.decodeInstance] using binding

theorem FrameProgram.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {raw compiled locals results functions}
    (program : FrameProgram before raw compiled locals results functions) :
    FrameProgram after raw compiled locals results functions := by
  refine ⟨?_,program.checked,program.fetchBound,program.localSlots,program.epilogue⟩
  obtain ⟨inst,found,code,table⟩ := program.lookup
  exact ⟨inst,by simpa only [metadata.instances] using found,code,table.store_metadata metadata⟩

theorem SavedFrame.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec raw source waiting childBase}
    (saved : SavedFrame before exec raw source waiting childBase) :
    SavedFrame after exec raw source waiting childBase := by
  refine ⟨saved.binding.store_metadata metadata,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,functions,targets,next,output,program.store_metadata metadata,point⟩

theorem SavedFrames.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec raws sources waiting childBase}
    (saved : SavedFrames before exec raws sources waiting childBase) :
    SavedFrames after exec raws sources waiting childBase := by
  induction saved with
  | nil waiting => exact .nil waiting
  | cons head tail ih => exact .cons (head.store_metadata metadata) ih

theorem ActiveFrame.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec raw source}
    (active : ActiveFrame before exec raw source) : ActiveFrame after exec raw source := by
  refine ⟨active.binding.store_metadata metadata,active.slots,?_⟩
  obtain ⟨compiled,functions,targets,next,output,pending,program,point⟩ := active.continuation
  exact ⟨compiled,functions,targets,next,output,pending,program.store_metadata metadata,point⟩

theorem FrameStackRel.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec sources}
    (stack : FrameStackRel before exec sources) : FrameStackRel after exec sources := by
  cases stack with
  | empty frames => exact .empty frames
  | active frames top saved => exact .active frames (top.store_metadata metadata) (saved.store_metadata metadata)

theorem ReadyTop.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec source}
    (ready : ReadyTop before exec source) : ReadyTop after exec source := by
  obtain ⟨raw,compiled,functions,targets,next,output,top,program,point⟩ := ready
  exact ⟨raw,compiled,functions,targets,next,output,top,program.store_metadata metadata,point⟩

theorem ReadyState.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec source}
    (ready : ReadyState before exec source) : ReadyState after exec source := by
  cases frames : source.frames with
  | nil => simpa only [ReadyState,frames] using ready
  | cons frame rest =>
    have top : ReadyTop before exec frame := by simpa only [ReadyState,frames] using ready
    simpa only [ReadyState,frames] using top.store_metadata metadata
end Exec.Interp
