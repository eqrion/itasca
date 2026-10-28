import Exec.Store.Instantiation.LinkedPreparedRun
import Exec.Store.Invariant.TypeStagingCauses
import Exec.Store.Invariant.FunctionStagingCauses
import Exec.Store.Api.TableStagingCauses
import Exec.Store.Api.MemoryStagingCauses
import Exec.Store.Api.GlobalStagingCauses
import Exec.Store.Initialization.ElementStagingCauses
import Exec.Store.Initialization.DataStagingCauses
import Exec.Store.Initialization.PrecheckCertifiedResourceCauses
import Exec.Store.Invariant.InstanceItemCauses
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

inductive PreparationPhase where
  | initial | linked | typed | functions | tables | memories | published | globals | elements | data

/-- Exact successful store-changing preparation computations. Reservations are
not transitions: their checked allocator law leaves their vectors unchanged.
The phase index fixes the source order and each callback retains its real input. -/
inductive PreparationResourcePath {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) :
    PreparationPhase → runtime.store.Store M → runtime.store.ModuleInst → Prop where
  | initial : PreparationResourcePath memory hooks floats allocator before module imports platform
      .initial before (emptyInstance module)
  | linked {inst} (run : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before,.Ok (),inst)) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .linked before inst
  | typed {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .linked store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) 0#usize inst =
        .ok (typeParts after (.Ok ()) next)) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .typed after next
  | functions {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .typed store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) 0#usize inst before.instances.len =
        .ok (typeParts after (.Ok ()) next)) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .functions after next
  | tables {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .functions store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) inst.tables.len inst =
        .ok (typeParts after (.Ok ()) next)) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .tables after next
  | memories {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .tables store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) inst.memories.len inst =
        .ok (typeParts after (.Ok ()) next)) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .memories after next
  | published {store inst instances}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .memories store inst)
      (run : alloc.vec.Vec.push store.instances inst = .ok instances) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .published
        {store with instances := instances} inst
  | globals {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .published store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize before.instances.len =
        .ok (storeParts after platform (.Ok ())))
      (found : after.instances.val[before.instances.len.val]? = some next) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .globals after next
  | elements {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .globals store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform (.Ok ()) 0#usize before.instances.len =
        .ok (storeParts after platform (.Ok ())))
      (found : after.instances.val[before.instances.len.val]? = some next) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .elements after next
  | data {store inst after next}
      (prior : PreparationResourcePath memory hooks floats allocator before module imports platform .elements store inst)
      (run : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store (.Ok ()) 0#usize before.instances.len =
        .ok (storeStateParts after (.Ok ())))
      (found : after.instances.val[before.instances.len.val]? = some next) :
      PreparationResourcePath memory hooks floats allocator before module imports platform .data after next

/-- Concrete refusal at a fixed phase, before further preparation occurs. -/
def PreparationRefusal {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule) (platform : P)
    (phase : PreparationPhase) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (error : runtime.ExecError) : Prop :=
  match phase with
  | .initial =>
    (error = .Exhausted .Objects ∧
      (before.limits.max_instances.val ≤ before.instances.length ∨
        Usize.max < moduleItems module ∨
        before.limits.max_instance_items.val < before.instance_items.val + moduleItems module)) ∨
    (error = .Exhausted .Allocation ∧
      (allocator.reserve (alloc.vec.Vec.new runtime.FuncAddr) module.module.env.func_types.len = .ok (false,alloc.vec.Vec.new runtime.FuncAddr) ∨
       allocator.reserve (alloc.vec.Vec.new runtime.TableAddr) module.module.env.table_types.len = .ok (false,alloc.vec.Vec.new runtime.TableAddr) ∨
       allocator.reserve (alloc.vec.Vec.new runtime.MemoryAddr) module.module.env.mem_types.len = .ok (false,alloc.vec.Vec.new runtime.MemoryAddr) ∨
       allocator.reserve (alloc.vec.Vec.new runtime.GlobalAddr) module.module.env.global_types.len = .ok (false,alloc.vec.Vec.new runtime.GlobalAddr)))
  | .linked =>
    (error = .Exhausted .Allocation ∧ allocator.reserve inst.types inst.module.module.env.types.len = .ok (false,inst.types)) ∨
    TypeStagingCause memory allocator store inst 0#usize error
  | .typed => FunctionStagingCause memory allocator store inst before.instances.len 0#usize error
  | .functions => ∃ limit, error = .Exhausted limit ∧ TableStagingCause memory allocator store inst inst.tables.len limit
  | .tables => ∃ limit, error = .Exhausted limit ∧ MemoryStagingCause memory allocator store inst inst.memories.len limit
  | .memories => error = .Exhausted .Allocation ∧ allocator.reserve store.instances 1#usize = .ok (false,store.instances)
  | .published => GlobalStagingCause memory hooks floats allocator store platform before.instances.len 0#usize error
  | .globals =>
    (error = .Exhausted .Allocation ∧ allocator.reserve inst.elems inst.module.module.env.elements.len = .ok (false,inst.elems)) ∨
    ElementStagingCause memory hooks floats allocator store platform before.instances.len 0#usize error
  | .elements =>
    (error = .Exhausted .Allocation ∧ allocator.reserve inst.datas inst.module.module.tail.data.len = .ok (false,inst.datas)) ∨
    DataStagingCause memory allocator store before.instances.len 0#usize error
  | .data => OffsetInitializerCause allocator store inst error

/-- Resource errors retain a concrete source-order preparation path and its
exact refusal. Nonresource errors have separate linking/bounds predicates. -/
def PrecommitResourceEvidence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (error : runtime.ExecError) : Prop :=
  ∀ limit, error = .Exhausted limit → ∃ phase store inst,
    PreparationResourcePath memory hooks floats allocator before module imports platform phase store inst ∧
    PreparationRefusal memory hooks floats allocator before module platform phase store inst error

theorem PrecommitResourceEvidence.at_phase {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {before : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {imports : Slice runtime.Extern} {platform : P} {phase store inst error}
    (path : PreparationResourcePath memory hooks floats allocator before module imports platform phase store inst)
    (refusal : PreparationRefusal memory hooks floats allocator before module platform phase store inst error) :
    PrecommitResourceEvidence memory hooks floats allocator before module imports platform error :=
  fun _ _ => ⟨phase,store,inst,path,refusal⟩
end Itasca.Runtime.Store
