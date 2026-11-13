import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Api.DefineTable
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Initialization.InitializerCertificates
import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Api.MemoryBindingLoop

/-!
Sections, each formerly its own module: AllocationErrors, PreparationInputs, PreparedInitializers, AllocationShape, AllocationStorage.
-/

/-! ## AllocationErrors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Error classification only: an ordinary return from the object-count gate
cannot manufacture a link, trap, or argument failure. -/
theorem room_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (out : core.result.Result Unit runtime.ExecError)
    (run : runtime.store.Store.room memory store = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.store.Store.room at run
  repeat' first
    | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ run; clear run; rename' rest => run)
    | split at run
    | (simp only [Result.ok.injEq] at run; subst out; trivial)

theorem reserve_errors {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize)
    (out : core.result.Result Unit runtime.ExecError × alloc.vec.Vec T)
    (run : runtime.reserve allocator values extra = .ok out) : ErrorAllowed ResourceError out.1 := by
  obtain ⟨answer, called⟩ := reserve_wrapper_eq allocator law values extra
  rw [called] at run
  simp only [Result.ok.injEq] at run
  rw [← run]
  cases answer <;> trivial

open Lean Meta Elab Tactic in
elab "allocation_error_effect " h:ident " using " allocator:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.reserve => `(tactic| have cause := reserve_errors $allocator $law _ _ _ $h)
    | ``runtime.store.Store.room => `(tactic| have cause := room_errors _ _ _ $h)
    | ``runtime.copy_type => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.copy_type_errors
      `(tactic| have cause := $theoremName $allocator $law _ _ $h)
    | ``runtime.store.Store.intern_type => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.intern_type_errors
      `(tactic| have cause := $theoremName _ $allocator $law _ _ _ $h)
    | ``runtime.store.copy_bytes => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.copy_bytes_errors
      `(tactic| have cause := $theoremName $allocator $law _ _ $h)
    | _ => throwError "not an allocation helper"
  evalTactic tac

macro "allocation_error_step " h:ident " using " allocator:term ", " law:term : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, ResourceError])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, ResourceError,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok]
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok, uncurry_apply_pair] at $h:ident)
  | split at $h:ident
  | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩
        repeat' (guard_hyp secondValue : Prod _ _; rcases secondValue with ⟨firstValue, secondValue⟩))
     | skip
     try allocation_error_effect called using $allocator, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | split at $h:ident)

theorem copy_type_errors {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType)
    (out : core.result.Result Itasca.wasm_types.FuncType runtime.ExecError)
    (run : runtime.copy_type allocator ty = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.copy_type at run
  repeat' allocation_error_step run using allocator, law

theorem intern_type_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
    (out : core.result.Result Usize runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.intern_type memory allocator store ty = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.intern_type at run
  repeat' allocation_error_step run using allocator, law

theorem copy_bytes_errors {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (out : core.result.Result (alloc.vec.Vec U8) runtime.ExecError)
    (run : runtime.store.copy_bytes allocator bytes = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.store.copy_bytes at run
  repeat' allocation_error_step run using allocator, law

theorem add_type_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_type memory allocator store inst index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_type at run
  repeat' allocation_error_step run using allocator, law

theorem add_function_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_function at run
  repeat' allocation_error_step run using allocator, law

theorem add_data_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.instantiate.Store.add_instance_data memory allocator store instanceIndex index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_data at run
  repeat' allocation_error_step run using allocator, law
end Itasca.Runtime.Store

end

/-! ## PreparationInputs -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The validator cache bounds every defined function's declared type index;
the type loop's complete map transfers that bound to canonical indices. -/
theorem cache_defined_type_bounds {module : runtime.compiler.ExecutableModule}
    {tables memories} (cache : Cache module.module.env tables memories)
    (indices : alloc.vec.Vec Usize)
    (complete : indices.length = module.module.env.types.length) :
    ∀ idx ∈ module.module.env.func_type_indices.val, idx.val < indices.length := by
  intro idx member
  have allMember : idx ∈ importedFuncs module.module.env.imports.val ++ module.module.env.func_type_indices.val :=
    List.mem_append_right _ member
  obtain ⟨position, bound, found⟩ := List.mem_iff_getElem.mp allMember
  have typeBound : position < module.module.env.func_types.val.length := by rw [← cache.funcs.length_eq]; exact bound
  obtain ⟨resolved, same⟩ := cache.funcs.get bound typeBound
  simp only [List.get_eq_getElem, found] at resolved
  simpa only [complete] using resolved

/-- The issued source environment already bounds the combined imported and
defined function-map length. No extra vector-capacity premise is needed. -/
theorem LinkedMaps.function_capacity {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.funcs.length + module.module.env.func_type_indices.val.length ≤ Usize.max := by
  have length := cache.funcs.length_eq
  have imported := maps.funcs.length_eq
  have maximum := module.module.env.func_types.property
  simp only [List.length_append] at length
  change inst.funcs.val.length + module.module.env.func_type_indices.val.length ≤ Usize.max
  omega

/-- Once all defined functions are added, the map count is exactly the source
function count used by constant-expression ref.func validation. -/
theorem complete_function_count {module : runtime.compiler.ExecutableModule}
    {tables memories} (cache : Cache module.module.env tables memories)
    (imported defined : Nat) (imports : imported = (importedFuncs module.module.env.imports.val).length)
    (complete : defined = imported + module.module.env.func_type_indices.val.length) :
    defined = module.module.env.func_types.val.length := by
  have length := cache.funcs.length_eq
  simp only [List.length_append] at length
  omega

end Itasca.Runtime.Store

end

/-! ## PreparedInitializers -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem LinkedMaps.table_start {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.tables.length ≤ module.module.env.table_types.val.length ∧
    ∀ address ∈ inst.tables.val, address.index.val < store.tables.length := by
  constructor
  · have mapCount := maps.tables.length_eq
    rw [cache.tables, List.length_append]
    change inst.tables.val.length ≤ _
    omega
  · intro address member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < (importedTables module.module.env.imports.val).length := by
      rw [maps.tables.length_eq]; exact bound
    obtain ⟨_, table, issued, _, _⟩ := maps.tables.get sourceBound bound
    simp only [List.get_eq_getElem, found] at issued
    exact (List.getElem?_eq_some_iff.mp issued).1

theorem LinkedMaps.memory_start {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.memories.length ≤ module.module.env.mem_types.val.length ∧
    ∀ address ∈ inst.memories.val, address.index.val < store.memories.length := by
  constructor
  · have mapCount := maps.memories.length_eq
    rw [cache.memories, List.length_append]
    change inst.memories.val.length ≤ _
    omega
  · intro address member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < (importedMems module.module.env.imports.val).length := by
      rw [maps.memories.length_eq]; exact bound
    obtain ⟨_, memory, issued, _⟩ := maps.memories.get sourceBound bound
    simp only [List.get_eq_getElem, found] at issued
    exact (List.getElem?_eq_some_iff.mp issued).1

/-- Source global definitions extend the exact linked imported prefix. -/
theorem LinkedMaps.global_capacity {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.globals.length + module.module.env.globals.val.length ≤ Usize.max := by
  have mapped := maps.globals.length_eq
  have capacity := module.module.env.global_types.property
  rw [cache.globals, List.length_append, List.length_map] at capacity
  change inst.globals.val.length + module.module.env.globals.val.length ≤ Usize.max
  omega

/-- Compose the structural results of linking and the four preparation loops.
The hypotheses are exact map counts/lookups and preserved fields, rather than
assumptions about evaluation or instantiation correctness. -/
theorem prepared_initializer_bindings {M : Type} (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (retained : StagedPrefix before store)
    (source : inst.module = seed.module) (globalMap : inst.globals = seed.globals)
    (globals : store.globals = before.globals)
    (functions : inst.funcs.val.length = seed.module.module.env.func_types.val.length)
    (functionAddresses : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (tableCount : inst.tables.val.length = seed.module.module.env.table_types.val.length)
    (memoryCount : inst.memories.val.length = seed.module.module.env.mem_types.val.length)
    (tableAddresses : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length) :
    InitializerBindings store inst ∧ InitializerImports store inst ∧ InitializerSegmentBindings store inst := by
  have functionGrowth : before.funcs.length ≤ store.funcs.length := by
    have lengths := congrArg List.length retained.funcs
    simp only [List.length_take] at lengths
    change before.funcs.val.length ≤ store.funcs.val.length
    omega
  have externalGrowth : before.externs.length ≤ store.externs.length := by rw [retained.externs]
  refine ⟨⟨functionAddresses, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, tableAddresses, memoryAddresses⟩⟩
  · intro global member
    rw [globals] at member
    exact GlobalShape.mono before store functionGrowth externalGrowth global (shape.globals global member)
  · simp only [source, functions, le_refl]
  · intro index ty found imported
    obtain ⟨address, global, mapped, issued, same⟩ := maps.global_resolution cache index ty
      (by simpa only [source] using found) (by simpa only [source] using imported)
    exact ⟨address, global, by simpa only [globalMap] using mapped, by simpa only [globals] using issued, same⟩
  · simp only [source, tableCount, le_refl]
  · simp only [source, memoryCount, le_refl]

end Itasca.Runtime.Store

end

/-! ## AllocationShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Allocated values and resource counters during instantiation. Function/module
links and instance-item accounting are completed after the provisional instance
has received its maps; no execution property is included here. -/
structure AllocationShape {M : Type} (view : M → Slice U8) (store : runtime.store.Store M) : Prop where
  identity : 0 < store.id.val
  memories : ∀ memory ∈ store.memories.val, MemoryShape view memory
  tables : ∀ table ∈ store.tables.val, TableShape store table
  globals : ∀ global ∈ store.globals.val, GlobalShape store global
  elements : ∀ element ∈ store.elems.val, ∀ word ∈ element.refs.val, ReferenceShape store element.ty word
  canonicalTypes : (store.types.val.map decodeFuncType).Nodup
  objectLimit : objectCount store ≤ store.limits.max_objects.val
  signatureAccounting : store.signature_values.val = (store.types.val.map fun ty => ty.params.length + ty.results.length).sum
  signatureLimit : store.signature_values.val ≤ store.limits.max_signature_values.val
  memoryAccounting : store.memory_bytes.val = (store.memories.val.map fun memory => (view memory.buf).length).sum
  memoryLimit : store.memory_bytes.val ≤ store.limits.max_memory_bytes.val
  tableAccounting : store.table_elements.val = (store.tables.val.map fun table => table.elements.length).sum
  tableLimit : store.table_elements.val ≤ store.limits.max_table_elements.val

theorem Shape.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) : AllocationShape view store :=
  ⟨shape.identity, shape.memories, shape.tables, shape.globals, shape.elements,
    shape.canonicalTypes, shape.object_count_bound, shape.signatureAccounting, shape.signatureLimit,
    shape.memoryAccounting, shape.memoryLimit, shape.tableAccounting, shape.tableLimit⟩

theorem AllocationShape.replace_instances {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : AllocationShape view store) (instances : alloc.vec.Vec runtime.store.ModuleInst) :
    AllocationShape view {store with instances} := by
  cases shape
  constructor <;> assumption

/-- Canonical type interning extends only its charged signature vector. -/
theorem InternEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {ty result} (effect : InternEffect store ty result) (shape : AllocationShape view store) :
    AllocationShape view result.2 := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, found, rfl⟩ |
    ⟨types, count, appended, fresh, room, counted, limited, rfl⟩
  · exact shape
  · exact shape
  · constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · simpa only [ReferenceShape] using shape.elements
    · simp [appended, List.nodup_append, shape.canonicalTypes]
      intro existing member equal
      have same := decode_func_type_injective equal
      subst existing
      exact fresh member
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · simp [appended, counted, shape.signatureAccounting, Nat.add_assoc]
    · exact limited
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem TypeStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : TypeStageEffect store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, addresses, interned, mapped, success, next⟩
  · exact shape
  · exact interned.allocated shape

/-- A newly allocated function may name the provisional instance, while all
pre-existing references remain valid under the extended function vector. -/
theorem FunctionStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst instanceIndex index signature out} (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (shape : AllocationShape view store) : AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, room, rfl⟩
  · exact shape
  · have grown : store.funcs.length ≤ functions.length := by simp [appended]
    constructor
    · exact shape.identity
    · exact shape.memories
    · intro table member
      exact TableShape.mono store _ grown (by simp) table (shape.tables table member)
    · intro global member
      exact GlobalShape.mono store _ grown (by simp) global (shape.globals global member)
    · intro element member word contained
      exact ReferenceShape.mono store _ grown (by simp) _ _ (shape.elements element member word contained)
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

end Itasca.Runtime.Store

end

/-! ## AllocationStorage -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : TableStageEffect store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, fit, room, counted, limited, rfl⟩
  · exact shape
  · have canonical : TableShape store {elements, ty := ty.elem, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp [zeros]
        scalar_tac
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have bound := fit.2
        simp only [maximumEq] at bound
        simpa [zeros] using bound.1
      · intro word member
        simp only [zeros, List.mem_replicate] at member
        rw [member.2]
        exact Or.inl rfl
    constructor
    · exact shape.identity
    · exact shape.memories
    · intro table member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [TableShape, ReferenceShape] using shape.tables table old
      · simpa only [TableShape, ReferenceShape] using canonical
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · simpa only [ReferenceShape] using shape.elements
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · simp [appended, zeros, counted, shape.tableAccounting]
    · exact limited

theorem MemoryStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : MemoryStageEffect view store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, fit, room, counted, limited, rfl⟩
  · exact shape
  · have size : (view buffer).length = ty.limits.min.val * 65536 := by simpa using congrArg List.length zeros
    have canonical : MemoryShape view {buf := buffer, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp [size]
      · simpa [size] using fit.1
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have bound := fit.2
        simp only [maximumEq] at bound
        simpa [size] using bound
    constructor
    · exact shape.identity
    · intro memory member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact shape.memories memory old
      · exact canonical
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · simpa only [ReferenceShape] using shape.elements
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · simp [appended, counted, shape.memoryAccounting]
    · exact limited
    · exact shape.tableAccounting
    · exact shape.tableLimit

end Itasca.Runtime.Store

end
