import Itasca.Runtime.Interp.Relations.StackRelation

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp
