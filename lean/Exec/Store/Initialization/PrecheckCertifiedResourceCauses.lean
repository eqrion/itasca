import Exec.Store.Initialization.InitializerCertificates
import Exec.Store.Initialization.PrecheckResourceLoops

/-! Full Wasm1 precommit checks derived from retained compiler maps and canonical
validator segment typing. Every path returns normally without changing the
store or invoking embedding hooks. -/
namespace Exec.Store
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_precheck_certified_resource_causes (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckResourceCause allocator view store inst) status)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    runtime.store.instantiate.Store.instantiate_inner_loop10 memory hooks floats allocator store platform status 0#usize instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) finalStatus ⦄ := by
  apply element_precheck_loop_resource_causes memory hooks floats allocator law view store platform instIndex 0#usize inst status
    allowed found bindings ?_ (by simp)
  intro index bound
  let segment := inst.module.module.env.elements.val[index.val]
  have read : inst.module.module.env.elements.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  exact ⟨segment, read, element_precheck_certificate store inst index segment compiled read
    (valid segment (List.mem_of_getElem? read)) bindings imports segments⟩

theorem data_precheck_certified_resource_causes (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckResourceCause allocator view store inst) status)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.ModuleData.Valid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    runtime.store.instantiate.Store.instantiate_inner_loop11 memory hooks floats allocator store platform status 0#usize instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) finalStatus ⦄ := by
  apply data_precheck_loop_resource_causes memory hooks floats allocator law view memoryLaws store platform instIndex 0#usize inst status
    allowed found bindings ?_ (by simp)
  intro index bound
  let segment := inst.module.module.tail.data.val[index.val]
  have read : inst.module.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  exact ⟨segment, read, data_precheck_certificate store inst index segment compiled read
    (valid segment (List.mem_of_getElem? read)) bindings imports segments⟩

end Exec.Store
