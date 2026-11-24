import Itasca.Runtime.Interp.Definitions
import Itasca.Results.Definitions.Store.State
import Itasca.Runtime.Compiler.Local.Definitions

namespace Itasca.Store
open Aeneas Aeneas.Std

def objectCount {M : Type} (s : runtime.store.Store M) : Nat :=
  s.funcs.length + s.tables.length + s.memories.length + s.globals.length +
    s.externs.length + s.types.length

end Itasca.Store

section StorePreparation

/-!
### Unpublished store preparation

Instance seeds, preflight charges, reached calls and retained prefixes describe staging before publication. Resource causes refer to the actual reached calls.
-/

section

/-!
## Store preparation vocabulary

Source-sized metadata charges and prepublication errors describe instantiation
without exposing unpublished instance records or loop tuples.
-/

/-!
## Source metadata charge

`moduleItems` counts address-map entries and element initializer entries. These
source quantities determine the per-instance metadata quota.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- The retained-map charge used by the actual instantiation preflight. -/
def moduleItems (module : runtime.compiler.ExecutableModule) : Nat :=
  module.module.env.types.length + module.module.env.func_types.length +
  module.module.env.table_types.length + module.module.env.mem_types.length +
  module.module.env.global_types.length + module.module.env.elements.length +
  module.module.tail.data.length +
  (module.module.env.elements.val.map fun element => element.init.length).sum

end Itasca.Store

/-!
## Prepublication errors

`PrecommitError` describes errors reported before publication, when the caller's
original store is retained.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std


end Itasca.Store

end

/-!
## Signature-copy requests

A signature copy reserves space for its source parameter and result types.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- A signature copy may refuse either of its two exact empty-vector requests. -/
def TypeCopyRefusal {A : Type} (allocator : runtime.platform.Alloc A)
    (ty : Itasca.wasm_types.FuncType) : Prop :=
  allocator.reserve (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.params.len =
    .ok (false,alloc.vec.Vec.new Itasca.wasm_types.ValueType) ∨
  allocator.reserve (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.results.len =
    .ok (false,alloc.vec.Vec.new Itasca.wasm_types.ValueType)

end Itasca.Store


end StorePreparation

section StoreAllocationCauses

/-!
### Object allocation refusal causes

Memory, table, function and signature allocation distinguish quota thresholds
from refused source-sized requests.
-/

/-!
## Memory and table allocation causes

Memory and table refusals distinguish storage quotas, vector reservations and
requests to the embedding memory provider.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

def MemoryAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_memory_bytes.val < store.memory_bytes.val + ty.limits.min.val * 65536 ∨
      allocator.reserve store.memories 1#usize = .ok (false,store.memories)
  | _ => False

def NewMemoryResourceCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M)
    (ty : Itasca.wasm_types.MemType) (limit : runtime.ResourceLimit) : Prop :=
  MemoryAllocationCause allocator store ty limit ∨
    (limit = .Allocation ∧ (Usize.max < ty.limits.min.val * 65536 ∨
      ∃ requested : Usize, requested.val = ty.limits.min.val * 65536 ∧
        memory.new_zeroed requested = .ok none))

def TableAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_table_elements.val < store.table_elements.val + ty.limits.min.val ∨
      allocator.reserve (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min) =
        .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.tables 1#usize = .ok (false,store.tables)
  | _ => False

end Itasca.Store

section

/-!
## Function and type allocation causes

Canonical signature interning and function publication retain quota thresholds
and allocator refusal witnesses.
-/

/-!
## Function allocation causes

Type interning and function-staging calls retain the actual request or quota responsible
for a function allocation failure.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Concrete thresholds and reached allocator requests for creating one new
canonical signature. Existing signatures return before these checks. -/
def TypeInternResourceCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Objects =>
      Usize.max < ty.params.length + ty.results.length ∨
      store.limits.max_signature_values.val < store.signature_values.val + ty.params.length + ty.results.length ∨
      store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation =>
      allocator.reserve store.types 1#usize = .ok (false,store.types) ∨ TypeCopyRefusal allocator ty
  | _ => False

/-- Defined function publication has only the object-count gate and the exact
store function-vector reservation as resource rejection sites. -/
def FunctionAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.funcs 1#usize = .ok (false,store.funcs)
  | _ => False

end Itasca.Store


end

end StoreAllocationCauses

section StoreInitializerAllocationCauses

/-!
### Initializer allocation causes

Global, data and element refusals distinguish segment storage requests from
the small workspace needed to evaluate source initializers.
-/

/-!
## Global allocation causes

A global can exhaust the object quota or fail to reserve its store entry.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

def GlobalAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.globals 1#usize = .ok (false,store.globals)
  | _ => False

end Itasca.Store

/-!
## Data and element allocation causes

Payload allocation requests use source segment sizes. Initializer failures are
covered separately by the uniform three-word workspace budget.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Both exact allocation requests made when adding a passive data payload. -/
def DataAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (data : Itasca.metadata.Data) (error : runtime.ExecError) : Prop :=
  error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U8) data.init.len = .ok (false,alloc.vec.Vec.new U8) ∨
      allocator.reserve store.datas 1#usize = .ok (false,store.datas))

end Itasca.Store

end StoreInitializerAllocationCauses

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Conservative initialization budget, independent of emitted instructions.
Expression initialization uses at most two words and segment initialization at
most three. Allocation failure retains an actual refused slot or frame request. -/
def InitializationResourceDemand {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val < 3
  | .Exhausted .Allocation =>
      (∃ n : Usize, n.val ≤ 3 ∧ allocator.reserve (alloc.vec.Vec.new U64) n =
        .ok (false, alloc.vec.Vec.new U64)) ∨
      allocator.reserve (alloc.vec.Vec.new runtime.interp.Frame) 1#usize =
        .ok (false, alloc.vec.Vec.new runtime.interp.Frame)
  | _ => False

/-- Resource allowances retain their units: object identities, signature values,
linear-memory bytes and table elements are counted separately. -/
structure PreparationDemand where
  objects : Nat := 0
  signatures : Nat := 0
  memoryBytes : Nat := 0
  tableElements : Nat := 0

namespace PreparationDemand

/-- Including imported table and memory types makes the bound conservative:
preparation allocates only the module's definitions, never its imported objects. -/
def source (module : metadata.Module) : PreparationDemand :=
  { objects := module.env.types.length + module.env.func_type_indices.length +
      module.env.table_types.length + module.env.mem_types.length + module.env.globals.length
    signatures := (module.env.types.val.map fun ty => ty.params.length + ty.results.length).sum
    memoryBytes := (module.env.mem_types.val.map fun ty => ty.limits.min.val * 65536).sum
    tableElements := (module.env.table_types.val.map fun ty => ty.limits.min.val).sum }

end PreparationDemand

/-- A bounded refusal state has the original limits and consumes no more than
its source allowance. Bounding every quota counter is essential: an arbitrary
hypothetical store could otherwise justify any exhaustion error. Object payloads
and the order of allocation are deliberately absent from this arithmetic contract. -/
structure PreparationGrowth {M : Type} (before after : runtime.store.Store M)
    (demand : PreparationDemand) : Prop where
  limits : after.limits = before.limits
  objects : objectCount after ≤ objectCount before + demand.objects
  signatures : after.signature_values.val ≤ before.signature_values.val + demand.signatures
  memoryBytes : after.memory_bytes.val ≤ before.memory_bytes.val + demand.memoryBytes
  tableElements : after.table_elements.val ≤ before.table_elements.val + demand.tableElements

/-- An actual source element expression lacks initialization resources. The
compiled function and its emission certificate are not part of the explanation. -/
def ElementInitializationResource {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  ∃ (k : Usize), ∃ expr, k.val < segment.init.length ∧ segment.init.val[k.val]? = some expr ∧
    InitializationResourceDemand allocator store error

/-- Segment storage refusals retain their exact source-sized initial request,
final store-vector request, or source initializer witness. -/
def ElementPreparationResource {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M)
    (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  (error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U64) segment.init.len = .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.elems 1#usize = .ok (false,store.elems))) ∨
  ElementInitializationResource allocator store segment error

/-- Total source allowance for a hypothetical refusal state. Segment vectors
need separate bounds because they do not count toward the object quota. These
bounds prevent an arbitrarily large intermediate store from explaining failure. -/
structure PreparationBounds {M : Type} (before current : runtime.store.Store M)
    (source : metadata.Module) : Prop where
  growth : PreparationGrowth before current (PreparationDemand.source source)
  elements : current.elems.length ≤ before.elems.length + source.env.elements.length
  datas : current.datas.length ≤ before.datas.length + source.tail.data.length

/-- Preflight checks depend only on the starting store and source metadata.
The four address maps are initially empty and reserve their source namespace sizes. -/
def PreparationPreflight {M A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (error : runtime.ExecError) : Prop :=
  (error = .Exhausted .Objects ∧
    (before.limits.max_instances.val ≤ before.instances.length ∨
      Usize.max < moduleItems module ∨
      before.limits.max_instance_items.val < before.instance_items.val + moduleItems module)) ∨
  (error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new runtime.FuncAddr) module.module.env.func_types.len = .ok (false,alloc.vec.Vec.new runtime.FuncAddr) ∨
     allocator.reserve (alloc.vec.Vec.new runtime.TableAddr) module.module.env.table_types.len = .ok (false,alloc.vec.Vec.new runtime.TableAddr) ∨
     allocator.reserve (alloc.vec.Vec.new runtime.MemoryAddr) module.module.env.mem_types.len = .ok (false,alloc.vec.Vec.new runtime.MemoryAddr) ∨
     allocator.reserve (alloc.vec.Vec.new runtime.GlobalAddr) module.module.env.global_types.len = .ok (false,alloc.vec.Vec.new runtime.GlobalAddr)))

/-- Further metadata reservations use empty source-sized maps or extend the
original instance vector by one entry. Their requests need no execution history. -/
def PreparationMetadataRefusal {M A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (source : metadata.Module) (error : runtime.ExecError) : Prop :=
  error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new Usize) source.env.types.len = .ok (false,alloc.vec.Vec.new Usize) ∨
     allocator.reserve (alloc.vec.Vec.new Usize) source.env.elements.len = .ok (false,alloc.vec.Vec.new Usize) ∨
     allocator.reserve (alloc.vec.Vec.new Usize) source.tail.data.len = .ok (false,alloc.vec.Vec.new Usize) ∨
     allocator.reserve before.instances 1#usize = .ok (false,before.instances))

/-- A source declaration accounts for the refused operation. This disjunction
classifies resources, not the order in which an implementation allocates them. -/
def PreparationResourceRefusal {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (current : runtime.store.Store M)
    (source : metadata.Module) (error : runtime.ExecError) : Prop :=
  (∃ ty ∈ source.env.types.val, TypeInternResourceCause allocator current ty error) ∨
  (0 < source.env.func_type_indices.val.length ∧ FunctionAllocationCause allocator current error) ∨
  (∃ limit, error = .Exhausted limit ∧ ∃ ty ∈ source.env.table_types.val,
    TableAllocationCause allocator current ty limit) ∨
  (∃ limit, error = .Exhausted limit ∧ ∃ ty ∈ source.env.mem_types.val,
    NewMemoryResourceCause memory allocator current ty limit) ∨
  (0 < source.env.globals.val.length ∧
    (InitializationResourceDemand allocator current error ∨ GlobalAllocationCause allocator current error)) ∨
  (∃ segment ∈ source.env.elements.val, ElementPreparationResource allocator current segment error) ∨
  (∃ data ∈ source.tail.data.val, DataAllocationCause allocator current data error)

/-- Conservative preparation resource explanation, independent of helper calls,
loop numbering and provisional instance records. A refusal state is bounded by
the complete source allowance, including source-sized segment vectors. Signature
reuse and imported objects can make actual consumption smaller.
Nonresource errors are classified separately by the instantiation contract. -/
def PreparationResources {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (error : runtime.ExecError) : Prop :=
  ∀ limit, error = .Exhausted limit →
    PreparationPreflight allocator before module error ∨
    PreparationMetadataRefusal allocator before module.module error ∨
    ∃ current, PreparationBounds before current module.module ∧
      PreparationResourceRefusal memory allocator current module.module error

end Itasca.Store


/-! Internal helper vocabulary used by construction proofs. -/

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

def elementValueType : Itasca.wasm_types.ElemType → Itasca.wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

def storeParts {M P : Type} (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) :=
  (store.id, store.limits, store.funcs, store.types, store.tables, store.memories,
    store.globals, store.instances, store.elems, store.datas, store.externs,
    store.instance_items, store.signature_values, store.memory_bytes, store.table_elements,
    platform, status)

def typeParts {M : Type} (store : runtime.store.Store M)
    (status : core.result.Result Unit runtime.ExecError) (inst : runtime.store.ModuleInst) :=
  (store, status, inst.module, inst.types, inst.funcs, inst.tables, inst.memories, inst.globals, inst.elems, inst.datas)

def emptyInstance (module : runtime.compiler.ExecutableModule) : runtime.store.ModuleInst := {
  module := module, types := alloc.vec.Vec.new Usize,
  funcs := alloc.vec.Vec.new runtime.FuncAddr, tables := alloc.vec.Vec.new runtime.TableAddr,
  memories := alloc.vec.Vec.new runtime.MemoryAddr, globals := alloc.vec.Vec.new runtime.GlobalAddr,
  elems := alloc.vec.Vec.new Usize, datas := alloc.vec.Vec.new Usize }

def ForeignExtern {M : Type} (s : runtime.store.Store M) : runtime.Extern → Prop
  | .Func a => a.store ≠ s.id
  | .Table a => a.store ≠ s.id
  | .Memory a => a.store ≠ s.id
  | .Global a => a.store ≠ s.id

end Itasca.Store

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- A reference value whose private handle belongs to another store. Numeric
values and null references are never foreign. -/
def ForeignValue {M : Type} (s : runtime.store.Store M) : runtime.Value → Prop
  | .FuncRef (some a) => a.store ≠ s.id
  | .ExternRef (some a) => a.store ≠ s.id
  | _ => False

end Itasca.Store


/-! Exact preparation certificates retained only by the construction proof.
Public initialization resource explanations use a three-word source budget. -/
namespace Itasca.Store
open Aeneas Aeneas.Std SpecExt

/-- The refused synthetic function belongs to an actual source initializer
of this element segment; the store argument is the unchanged evaluation state. -/
def ElementInitializerCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  ∃ (k : Usize), ∃ functions function code expr,
    k.val < segment.init.length ∧
    inst.module.element_initializers.val[index.val]? = some functions ∧
    functions.val[k.val]? = some function ∧ segment.init.val[k.val]? = some expr ∧
    inst.module.functions.val[function.val]? = some code ∧
    Compiler.InitializerCode code expr (elementValueType segment.elem) ∧
    Interp.SyntheticPreparationCause allocator store code error

/-- Segment storage refusals retain their exact source-sized initial request,
final store-vector request, or source initializer witness. -/
def ElementAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  (error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U64) segment.init.len = .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.elems 1#usize = .ok (false,store.elems))) ∨
  ElementInitializerCause allocator store inst index segment error

/-- Exact setup cause for the actual compiled segment initializer. The function
lookup and checked syntactic program prevent an arbitrary slot demand witness. -/
def SegmentSetupCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (error : runtime.ExecError) : Prop :=
  ∃ code, module.functions.val[module.initialization.val]? = some code ∧
    Compiler.SegmentProgram module code ∧ Interp.SyntheticPreparationCause allocator store code error

/-- Internal calling convention for the source-based public resource contract. -/
def PrecommitResourceEvidence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (_hooks : runtime.platform.Platform P M)
    (_floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (_imports : Slice runtime.Extern) (_platform : P) (error : runtime.ExecError) : Prop :=
  PreparationResources memory allocator before module error

end Itasca.Store

/-! ## Store / Exports -/

section StoreExports

/-!
### Export descriptor bounds

Module and store export predicates retain namespace bounds and decoded-name conditions
required by the public store invariant.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Static export descriptors address the validated namespace and retain
unique source names. Both facts depend only on immutable module metadata. -/
structure ModuleExportBounds (env : Itasca.metadata.Env) : Prop where
  indices : ∀ entry ∈ env.exports.val, match entry.desc with
    | .Func index => index.val < env.func_types.length
    | .Table index => index.val < env.table_types.length
    | .Memory index => index.val < env.mem_types.length
    | .Global index => index.val < env.global_types.length
  names : (env.exports.val.map (fun entry => Itasca.Binary.nameOfBytes entry.name.val)).Nodup

/-- Every retained instance has bounded module export descriptors. -/
def ExportBounds {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ (index : Nat) (inst : runtime.store.ModuleInst), store.instances.val[index]? = some inst → ModuleExportBounds inst.module.module.env

end Itasca.Store

end StoreExports
namespace Itasca.Store
open Aeneas Aeneas.Std SpecExt Itasca.Representation
/-- Source syntax attached to one compiled instance and its ghost source bodies. -/
structure InstanceSyntax (code : CodeInterpretation) (index : Nat)
    (inst : runtime.store.ModuleInst) : Prop where
  /-- Every retained export name decodes to a well-formed specification name. -/
  exportNames : ∀ entry ∈ inst.module.module.env.exports.val,
    wf_name (Itasca.Binary.nameOfBytes entry.name.val)
  /-- The interpretation supplies well-formed syntax for each defined body. -/
  functionCodes : ∀ function, function < inst.module.module.env.func_type_indices.length →
    wf_funccode (code index inst.module function)

/-- Each retained instance carries its independently checked source syntax. -/
def StoreSyntax {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M) : Prop :=
  ∀ index inst, s.instances.val[index]? = some inst → InstanceSyntax code index inst

/-- Segment lengths come from validated binary counts. They remain explicit
structural bounds because dropped segments may be shorter than their sources. -/
structure SegmentBounds {M : Type} (s : runtime.store.Store M) : Prop where
  /-- Retained element segments fit the binary format's count space. -/
  elements : ∀ element ∈ s.elems.val, element.refs.length < 2^32
  /-- Retained data segments fit the binary format's count space. -/
  data : ∀ segment ∈ s.datas.val, segment.bytes.length < 2^32

structure SegmentAccounting {M : Type} (store : runtime.store.Store M) : Prop where
  elements : store.elems.length = (store.instances.val.map fun inst => inst.elems.length).sum
  datas : store.datas.length = (store.instances.val.map fun inst => inst.datas.length).sum
end Itasca.Store

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Resolve a validated raw descriptor through the instance address maps. -/
def resolveExport (inst : runtime.store.ModuleInst) (entry : Itasca.metadata.Export) : runtime.Extern :=
  match entry.desc with
  | .Func index => .Func (inst.funcs.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Table index => .Table (inst.tables.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Memory index => .Memory (inst.memories.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Global index => .Global (inst.globals.val.getD index.val ⟨0#usize, 0#usize⟩)

/-- First matching raw byte-name at or after the supplied cursor. -/
def exportSearch (inst : runtime.store.ModuleInst) (query : Slice U8) (index : Nat)
    (found : Option runtime.Extern) : Option runtime.Extern :=
  found.orElse fun _ => ((inst.module.module.env.exports.val.drop index).find?
    (fun entry => decide (entry.name.val = query.val))).map (resolveExport inst)

end Itasca.Store

/-!
## Unpublished store prefixes

`StagedPrefix` records the retained prefix across staging operations, supporting
rollback and publication reasoning.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Before the commit point, provisional objects extend existing vectors without
changing their retained prefixes. Counters restored by the wrapper are deliberately
absent. This is a staging relation, not a successful-store invariant. -/
structure StagedPrefix {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  limits : after.limits = before.limits
  funcs : after.funcs.val.take before.funcs.length = before.funcs.val
  types : after.types.val.take before.types.length = before.types.val
  tables : after.tables.val.take before.tables.length = before.tables.val
  memories : after.memories.val.take before.memories.length = before.memories.val
  globals : after.globals.val.take before.globals.length = before.globals.val
  instances : after.instances.val.take before.instances.length = before.instances.val
  elems : after.elems.val.take before.elems.length = before.elems.val
  datas : after.datas.val.take before.datas.length = before.datas.val
  externs : after.externs = before.externs
  instanceItems : after.instance_items = before.instance_items

end Itasca.Store

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Representation

def TableGrowth {M : Type} (s : runtime.store.Store M) (index : Usize)
    (delta : U32) (value : U64) (result : U32 × runtime.store.Store M) : Prop :=
  (result.1 = core.num.U32.MAX ∧ result.2 = s) ∨
  ∃ old : runtime.store.TableInst, ∃ elements : alloc.vec.Vec U64, ∃ count : Usize,
    s.tables.val[index.val]? = some old ∧
    elements.val = old.elements.val ++ List.replicate delta.val value ∧
    old.elements.length + delta.val ≤ U32.max ∧
    count.val = s.table_elements.val + delta.val ∧
    count.val ≤ s.limits.max_table_elements.val ∧
    old.elements.length + delta.val ≤ (core.option.Option.unwrap_or old.maximum core.num.U32.MAX).val ∧
    result = (UScalar.cast .U32 (alloc.vec.Vec.len old.elements),
      {s with tables := s.tables.set index {old with elements := elements}, table_elements := count})

def MemoryGrowth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (result : U32 × runtime.store.Store M) : Prop :=
  (result.1 = core.num.U32.MAX ∧ decodeStore view code result.2 = decodeStore view code s ∧
    (result.2 = s ∨ ∃ old : runtime.store.MemInst M, ∃ after : M,
      s.memories.val[index.val]? = some old ∧ view after = view old.buf ∧
      result.2 = {s with memories := s.memories.set index {old with buf := after}})) ∨
  ∃ old : runtime.store.MemInst M, ∃ after : M, ∃ count : Usize,
    s.memories.val[index.val]? = some old ∧
    (view after).val = (view old.buf).val ++ List.replicate (delta.val * 65536) 0#u8 ∧
    count.val = s.memory_bytes.val + delta.val * 65536 ∧
    count.val ≤ s.limits.max_memory_bytes.val ∧
    (view old.buf).length / 65536 + delta.val ≤ 65536 ∧
    (view old.buf).length / 65536 + delta.val ≤
      (core.option.Option.unwrap_or old.maximum 65536#u32).val ∧
    result.1.val = (view old.buf).length / 65536 ∧
    result.2 = {s with memories := s.memories.set index {old with buf := after}, memory_bytes := count}

end Itasca.Store
