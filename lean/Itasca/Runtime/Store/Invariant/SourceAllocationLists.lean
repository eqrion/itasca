import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Api.MemoryAllocationLoop
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Preparation.StagingAddresses
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Preparation.PreparationInputs
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Preparation.AllocationShape
import Itasca.Runtime.Store.Initialization.ElementSourceStaging
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Compiler.Local.Source.SourceSlice

/-!
Sections, each formerly its own module: AllocatedTableLoop, AllocatedTypeLoop, AllocatedFunctionLoop, FunctionAllocatedPreparation, FunctionPreparation, InstanceItems, ShapeAssembly, ItemErrors, SourceAllocationLists.
-/

/-! ## AllocatedTableLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table allocation loop establishes complete issued table maps,
while retaining all old store objects and all other provisional maps. -/
theorem table_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (owners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (count : inst.tables.length = start.val)
    (matching : TableTypeMap store (seed.module.module.env.table_types.val.take start.val) inst.tables.val) :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (∀ address ∈ next.tables.val, address.store = after.id) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        (status = .Ok () → TableTypeMap after seed.module.module.env.table_types.val next.tables.val) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      (∀ address ∈ state.2.2.2.tables.val, address.store = state.1.id) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → TableTypeMap state.1 (seed.module.module.env.table_types.val.take state.2.2.1.val) state.2.2.2.tables.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated currentIssued currentOwners indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, by simp, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.table_types.val.length := by simpa only [source] using within
        have room : currentInst.tables.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_table_effect memory allocator law current currentInst index
          actualBound bound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with tables := after.tables, table_elements := after.table_elements} := by
          calc
            after = {current with tables := after.tables, table_elements := after.table_elements} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with tables := nextInst.tables} := by
          calc
            nextInst = {currentInst with tables := nextInst.tables} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated,
          effect.issued currentIssued, effect.owners currentOwners, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTyped := effect.table_types (typed rfl) success
          simpa only [source, increment, List.take_succ_eq_append_getElem within] using nextTyped
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, ?_, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd, List.take_length] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, issued, owners, startBound, (fun _ => count), (fun _ => matching)⟩

end Itasca.Runtime.Store

end

/-! ## AllocatedTypeLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Type canonicalization is total and preserves all other prepared maps. Its
successful type vector resolves every source signature to an exact store entry. -/
theorem type_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize) (startBound : start.val ≤ seed.module.module.env.types.val.length)
    (changed : store = {before with types := store.types, signature_values := store.signature_values})
    (instChanged : inst = {seed with types := inst.types})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (entries : TypeEntries store (seed.module.module.env.types.val.take start.val) inst.types.val) :
    runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with types := after.types, signature_values := after.signature_values} ∧
        next = {seed with types := next.types} ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (status = .Ok () → TypeEntries after seed.module.module.env.types.val next.types.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop3
  apply loop.spec_decr_nat (fun state => seed.module.module.env.types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with types := state.1.types, signature_values := state.1.signature_values} ∧
      state.2.2.2 = {seed with types := state.2.2.2.types} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ state.2.2.1.val ≤ seed.module.module.env.types.val.length ∧
      (state.2.1 = .Ok () → TypeEntries state.1 (seed.module.module.env.types.val.take state.2.2.1.val)
        state.2.2.2.types.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, indexBound, typing⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated indexBound typing ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop3.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, currentAllocated, by simp⟩
      | Ok value =>
        cases value
        have typed := typing rfl
        have mapSize : currentInst.types.val.length = index.val := by
          have lengths := typed.length_eq
          simpa [List.length_take, Nat.min_eq_left indexBound] using lengths.symm
        have maximum := seed.module.module.env.types.property
        have room : currentInst.types.length < Usize.max := by change currentInst.types.val.length < Usize.max; omega
        have actualBound : index.val < currentInst.module.module.env.types.val.length := by simpa only [source] using within
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_type_effect memory allocator law current currentInst index actualBound bound room
          as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with types := after.types, signature_values := after.signature_values} := by
          calc
            after = {current with types := after.types, signature_values := after.signature_values} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with types := nextInst.types} := by
          calc
            nextInst = {currentInst with types := nextInst.types} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated, ?_, ?_, ?_⟩
        · omega
        · intro success
          have extended := effect.entries success typed
          rw [increment, List.take_succ_eq_append_getElem within]
          simpa only [source] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, currentAllocated, ?_⟩
      intro success
      simpa only [atEnd, List.take_length] using typing success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, startBound, fun _ => entries⟩

end Itasca.Runtime.Store

end

/-! ## AllocatedFunctionLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max)
    (initialTypes : List functype) (definedTypes : List Itasca.wasm_types.FuncType)
    (resolves : List.Forall₂ (Itasca.ModuleEnv.Resolves seed.module.module.env.types.val)
      seed.module.module.env.func_type_indices.val definedTypes)
    (entries : TypeEntries before seed.module.module.env.types.val seed.types.val)
    (table : Interp.FunctionTable store inst (initialTypes ++ (definedTypes.take start.val).map decodeFuncType))
    (stagedFunctions : StagedFunctionSignatures before store instanceIndex definedTypes) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ∧
        (status = .Ok () → Interp.FunctionTable after next (initialTypes ++ definedTypes.map decodeFuncType)) ∧
        StagedFunctionSignatures before after instanceIndex definedTypes ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val) ∧
      (state.2.1 = .Ok () → Interp.FunctionTable state.1 state.2.2.2
        (initialTypes ++ (definedTypes.take state.2.2.1.val).map decodeFuncType)) ∧
      StagedFunctionSignatures before state.1 instanceIndex definedTypes)
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, currentIssued, indexBound, counting, matching, currentStaged⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated currentIssued indexBound counting matching currentStaged ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentAllocated, currentIssued, by simp, by simp, currentStaged⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have rawBound : index.val < definedTypes.length := by rw [← resolves.length_eq]; exact within
        have typedSource := resolves.get within rawBound
        simp only [List.get_eq_getElem] at typedSource
        have currentStoreTypes := congrArg runtime.store.Store.types currentChanged
        dsimp only at currentStoreTypes
        have currentEntries : TypeEntries current currentInst.module.module.env.types.val currentInst.types.val := by
          simpa only [TypeEntries, source, types, currentStoreTypes] using entries
        have actualResolved : Itasca.ModuleEnv.Resolves currentInst.module.module.env.types.val
            currentInst.module.module.env.func_type_indices.val[index.val] definedTypes[index.val] := by
          simpa only [source] using typedSource
        have signature := type_entries_resolve currentEntries _ _ actualResolved
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated,
          effect.issued currentIssued, ?_, ?_, ?_, effect.signatures currentStaged rawBound signature.2, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTable := effect.function_table (matching rfl) signature.2 success
          simpa only [increment, List.take_succ_eq_append_getElem rawBound,
            List.map_append, List.map_singleton, List.append_assoc] using nextTable
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentAllocated, currentIssued, ?_, ?_, currentStaged⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        have size : index.val = definedTypes.length := atEnd.trans resolves.length_eq
        simpa only [size, List.take_length] using matching success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, issued, startBound, (fun _ => count), (fun _ => table), stagedFunctions⟩

end Itasca.Runtime.Store

end

/-! ## FunctionAllocatedPreparation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete function-allocation loop constructs the full canonical
signature table and exact source-index metadata for every newly staged entry.
Its premises are the maps already established by linking/type interning. -/
theorem prepare_function_allocated {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex : Usize)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (entries : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable store inst
      ((inst.module.module.env.func_types.val.take (importedFuncs inst.module.module.env.imports.val).length).map decodeFuncType)) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) 0#usize inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {store with funcs := after.funcs} ∧ next = {inst with funcs := next.funcs} ∧
        StagedPrefix store after ∧ objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (status = .Ok () → Interp.FunctionTable after next (inst.module.module.env.func_types.val.map decodeFuncType)) ∧
        StagedFunctionSignatures store after instanceIndex
          (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length) ⦄ := by
  let imported := (importedFuncs inst.module.module.env.imports.val).length
  let defined := inst.module.module.env.func_types.val.drop imported
  have rawLength : imported + inst.module.module.env.func_type_indices.val.length = inst.module.module.env.func_types.val.length := by
    simpa only [List.length_append] using cache.funcs.length_eq
  have initialCount : inst.funcs.length = imported := by
    have same := table.length_eq
    simp only [List.length_map, List.length_take] at same
    change inst.funcs.val.length = imported
    change inst.funcs.val.length = Nat.min imported inst.module.module.env.func_types.val.length at same
    have importedBound : imported ≤ inst.module.module.env.func_types.val.length := by omega
    simpa only [Nat.min_eq_left importedBound] using same
  have capacity : inst.funcs.length + inst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
    rw [initialCount, rawLength]
    exact inst.module.module.env.func_types.property
  have typeBounds := cache_defined_type_bounds cache inst.types entries.length_eq.symm
  have definedResolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
      inst.module.module.env.func_type_indices.val defined := by
    simpa only [defined, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
  have checked  := function_allocated_loop memory allocator law view store store inst inst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) objectBound allocated typeBounds (function_table_issued table) (by simp) capacity
    ((inst.module.module.env.func_types.val.take imported).map decodeFuncType) defined definedResolves entries
    (by simpa using table) (.refl _ _ _)
  apply WP.spec_mono checked
  rintro out ⟨after, next, status, parts, changed, instChanged, retained, bound, afterAllocated, issued, count, complete, staged⟩
  refine ⟨after, next, status, parts, changed, instChanged, retained, bound, afterAllocated, ?_, staged⟩
  intro success
  have full := complete success
  simpa only [defined, ← List.map_append, List.take_append_drop] using full

end Itasca.Runtime.Store

end

/-! ## FunctionPreparation -/

section

/-!
Function signature preparation through its allocation loop. The loop transports signature lookup evidence into the prepared function certificate.
-/

/-! ## Function Signature Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_signature_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max)
    (initialTypes : List functype) (definedTypes : List Itasca.wasm_types.FuncType)
    (resolves : List.Forall₂ (Itasca.ModuleEnv.Resolves seed.module.module.env.types.val)
      seed.module.module.env.func_type_indices.val definedTypes)
    (entries : TypeEntries before seed.module.module.env.types.val seed.types.val)
    (table : Interp.FunctionTable store inst (initialTypes ++ (definedTypes.take start.val).map decodeFuncType))
    (stagedFunctions : StagedFunctionSignatures before store instanceIndex definedTypes) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ∧
        (status = .Ok () → Interp.FunctionTable after next (initialTypes ++ definedTypes.map decodeFuncType)) ∧
        StagedFunctionSignatures before after instanceIndex definedTypes ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val) ∧
      (state.2.1 = .Ok () → Interp.FunctionTable state.1 state.2.2.2
        (initialTypes ++ (definedTypes.take state.2.2.1.val).map decodeFuncType)) ∧
      StagedFunctionSignatures before state.1 instanceIndex definedTypes)
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, matching, currentStaged⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting matching currentStaged ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, by simp, currentStaged⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have rawBound : index.val < definedTypes.length := by rw [← resolves.length_eq]; exact within
        have typedSource := resolves.get within rawBound
        simp only [List.get_eq_getElem] at typedSource
        have currentStoreTypes := congrArg runtime.store.Store.types currentChanged
        dsimp only at currentStoreTypes
        have currentEntries : TypeEntries current currentInst.module.module.env.types.val currentInst.types.val := by
          simpa only [TypeEntries, source, types, currentStoreTypes] using entries
        have actualResolved : Itasca.ModuleEnv.Resolves currentInst.module.module.env.types.val
            currentInst.module.module.env.func_type_indices.val[index.val] definedTypes[index.val] := by
          simpa only [source] using typedSource
        have signature := type_entries_resolve currentEntries _ _ actualResolved
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_, effect.signatures currentStaged rawBound signature.2, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTable := effect.function_table (matching rfl) signature.2 success
          simpa only [increment, List.take_succ_eq_append_getElem rawBound,
            List.map_append, List.map_singleton, List.append_assoc] using nextTable
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, ?_, currentStaged⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        have size : index.val = definedTypes.length := atEnd.trans resolves.length_eq
        simpa only [size, List.take_length] using matching success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => table), stagedFunctions⟩

end Itasca.Runtime.Store

end

/-! ## Function Preparation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete function-allocation loop constructs the full canonical
signature table and exact source-index metadata for every newly staged entry.
Its premises are the maps already established by linking/type interning. -/
theorem prepare_function_signatures {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex : Usize)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (objectBound : objectCount store ≤ Usize.max)
    (entries : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable store inst
      ((inst.module.module.env.func_types.val.take (importedFuncs inst.module.module.env.imports.val).length).map decodeFuncType)) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) 0#usize inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {store with funcs := after.funcs} ∧ next = {inst with funcs := next.funcs} ∧
        StagedPrefix store after ∧ objectCount after ≤ Usize.max ∧
        (status = .Ok () → Interp.FunctionTable after next (inst.module.module.env.func_types.val.map decodeFuncType)) ∧
        StagedFunctionSignatures store after instanceIndex
          (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length) ⦄ := by
  let imported := (importedFuncs inst.module.module.env.imports.val).length
  let defined := inst.module.module.env.func_types.val.drop imported
  have rawLength : imported + inst.module.module.env.func_type_indices.val.length = inst.module.module.env.func_types.val.length := by
    simpa only [List.length_append] using cache.funcs.length_eq
  have initialCount : inst.funcs.length = imported := by
    have same := table.length_eq
    simp only [List.length_map, List.length_take] at same
    change inst.funcs.val.length = imported
    change inst.funcs.val.length = Nat.min imported inst.module.module.env.func_types.val.length at same
    have importedBound : imported ≤ inst.module.module.env.func_types.val.length := by omega
    simpa only [Nat.min_eq_left importedBound] using same
  have capacity : inst.funcs.length + inst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
    rw [initialCount, rawLength]
    exact inst.module.module.env.func_types.property
  have typeBounds := cache_defined_type_bounds cache inst.types entries.length_eq.symm
  have definedResolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
      inst.module.module.env.func_type_indices.val defined := by
    simpa only [defined, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
  have checked := function_signature_loop memory allocator law store store inst inst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) objectBound typeBounds (function_table_issued table) (by simp) capacity
    ((inst.module.module.env.func_types.val.take imported).map decodeFuncType) defined definedResolves entries
    (by simpa using table) (.refl _ _ _)
  apply WP.spec_mono checked
  rintro out ⟨after, next, status, parts, changed, instChanged, retained, bound, issued, count, complete, staged⟩
  refine ⟨after, next, status, parts, changed, instChanged, retained, bound, ?_, staged⟩
  intro success
  have full := complete success
  simpa only [defined, ← List.map_append, List.take_append_drop] using full

end Itasca.Runtime.Store

end

end

/-! ## InstanceItems -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem add_items_effect (items additional : Usize) :
    runtime.store.add_items items additional ⦃ out =>
      (out.1 = .Ok () ∧ out.2.val = items.val + additional.val) ∨
      (out = (.Err (.Exhausted .Objects), items) ∧ Usize.max < items.val + additional.val) ⦄ := by
  unfold runtime.store.add_items
  step as ⟨total, htotal⟩
  cases total with
  | none => simp only [WP.spec_ok]; exact Or.inr ⟨True.intro, htotal⟩
  | some total => simp only [WP.spec_ok]; exact Or.inl ⟨True.intro, htotal.2.1⟩

/-- The retained-map charge used by the actual instantiation preflight. -/
def moduleItems (module : runtime.compiler.ExecutableModule) : Nat :=
  module.module.env.types.length + module.module.env.func_types.length +
  module.module.env.table_types.length + module.module.env.mem_types.length +
  module.module.env.global_types.length + module.module.env.elements.length +
  module.module.tail.data.length +
  (module.module.env.elements.val.map fun element => element.init.length).sum

def moduleItemCounts (module : runtime.compiler.ExecutableModule) : Array Usize 7#usize :=
  Array.make 7#usize [module.module.env.types.len, module.module.env.func_types.len,
    module.module.env.table_types.len, module.module.env.mem_types.len,
    module.module.env.global_types.len, module.module.env.elements.len, module.module.tail.data.len]

theorem element_items_error (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (error : runtime.ExecError) :
    runtime.store.instantiate.Store.prepare_instance_loop1 module items (.Err error) start =
      .ok (items, .Err error) := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop1
  rw [loop.eq_def]
  simp only [runtime.store.instantiate.Store.prepare_instance_loop1.body,
    runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  split <;> simp [core.result.Result.is_ok]

/-- Passing the actual item limit supplies the store and fresh-instance vector
capacity required by the staged segment loops. Existing segment counts use the
reachable-store accounting invariant, rather than an unproved storage bound. -/
theorem instance_segment_capacity {M : Type} {view : M → Slice U8}
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (shape : Shape view store) (accounted : SegmentAccounting store)
    (items : Usize) (exactItems : items.val = moduleItems module)
    (fits : store.instance_items.val + items.val ≤ store.limits.max_instance_items.val) :
    store.elems.length + module.module.env.elements.length ≤ Usize.max ∧
    store.datas.length + module.module.tail.data.length ≤ Usize.max ∧
    module.module.env.global_types.length ≤ Usize.max ∧
    module.module.env.elements.length ≤ Usize.max ∧ module.module.tail.data.length ≤ Usize.max := by
  have elementBound := accounted.element_bound shape
  have dataBound := accounted.data_bound shape
  have limit := store.limits.max_instance_items.hmax
  have bounded : store.limits.max_instance_items.val ≤ Usize.max := by scalar_tac
  unfold moduleItems at exactItems
  omega

end Itasca.Runtime.Store

end

/-! ## ShapeAssembly -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

private theorem length_of_prefix {T : Type} {before after : List T}
    (retained : after.take before.length = before) : before.length ≤ after.length := by
  have size := congrArg List.length retained
  simp only [List.length_take] at size
  omega

theorem StagedPrefix.instance_shape {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) (inst : runtime.store.ModuleInst) (shape : InstanceShape before inst) :
    InstanceShape after inst :=
  InstanceShape.mono before after retained.identity.symm
    (length_of_prefix retained.types) (length_of_prefix retained.funcs)
    (length_of_prefix retained.tables) (length_of_prefix retained.memories)
    (length_of_prefix retained.globals) (length_of_prefix retained.elems)
    (length_of_prefix retained.datas) inst shape

theorem StagedPrefix.function_shape {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) (function : runtime.store.FuncInst) (shape : FunctionShape before function) :
    FunctionShape after function := by
  obtain ⟨signature, body⟩ := shape
  refine ⟨Nat.lt_of_lt_of_le signature (length_of_prefix retained.types), ?_⟩
  cases code : function.code with
  | Host id => trivial
  | Wasm instanceIndex functionIndex =>
    simp only [code] at body ⊢
    obtain ⟨inst, found, bound⟩ := body
    exact ⟨inst, Itasca.Runtime.Representation.lookup_prefix _ _ retained.instances found, bound⟩

/-- Retained functions and the concrete newly allocated source-index metadata
supply FunctionShape after the provisional instance has been published. -/
theorem staged_function_shapes {M : Type} {view : M → Slice U8}
    (before after : runtime.store.Store M) (shape : Shape view before)
    (retained : StagedPrefix before after) (inst : runtime.store.ModuleInst)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    ∀ function ∈ after.funcs.val, FunctionShape after function := by
  intro function member
  rcases staged function member with old | ⟨index, bound, code, signature⟩
  · exact retained.function_shape function (shape.functions function old)
  · have sizes := cache.funcs.length_eq
    simp only [List.length_append] at sizes
    have definedBound : index.val < inst.module.module.env.func_type_indices.length := by
      simp only [List.length_drop] at bound
      change index.val < inst.module.module.env.func_type_indices.val.length
      omega
    refine ⟨(List.getElem?_eq_some_iff.mp signature).1, ?_⟩
    simp only [code]
    exact ⟨inst, found, definedBound⟩

/-- A source-complete instance is charged exactly the preflight module total. -/
theorem InstanceShape.item_charge {M : Type} {store : runtime.store.Store M}
    (inst : runtime.store.ModuleInst) (shape : InstanceShape store inst) : instanceItems inst = moduleItems inst.module := by
  obtain ⟨types, functions, tables, memories, globals, elements, datas, rest⟩ := shape
  simp only [instanceItems, moduleItems, types, functions, tables, memories, globals, elements, datas]

private theorem append_singleton_of_prefix {T : Type} {before after : List T} {value : T}
    (retained : after.take before.length = before) (size : after.length = before.length + 1)
    (found : after[before.length]? = some value) : after = before ++ [value] := by
  apply List.ext_getElem?
  intro index
  by_cases old : index < before.length
  · have read := congrArg (fun values => values[index]?) retained
    simpa [List.getElem?_take, old, List.getElem?_append] using read
  · by_cases last : index = before.length
    · subst index
      simpa using found
    · have past : after.length ≤ index := by omega
      have pastAppend : (before ++ [value]).length ≤ index := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getElem?_eq_none past, List.getElem?_eq_none pastAppend]

/-- The final item charge assembles full Store.Shape from the actual allocated
inventory, the completed new instance, and concrete staged function metadata. -/
theorem shape_after_staging {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (allocated : AllocationShape view after) (retained : StagedPrefix before after)
    (inst : runtime.store.ModuleInst) (found : after.instances.val[before.instances.len.val]? = some inst)
    (instanceShape : InstanceShape after inst)
    (instanceCount : after.instances.length = before.instances.length + 1)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length))
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems inst.module)
    (limited : count.val ≤ after.limits.max_instance_items.val) :
    Shape view {after with instance_items := count} := by
  have instances : after.instances.val = before.instances.val ++ [inst] :=
    append_singleton_of_prefix retained.instances instanceCount found
  have charged := instanceShape.item_charge inst
  have functions := staged_function_shapes before after shape retained inst found cache staged
  constructor
  · exact allocated.identity
  · simpa only [FunctionShape] using functions
  · exact allocated.memories
  · simpa only [TableShape, ReferenceShape] using allocated.tables
  · simpa only [GlobalShape, ReferenceShape] using allocated.globals
  · simpa only [ReferenceShape] using allocated.elements
  · intro entry member
    simp only [instances, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact retained.instance_shape entry (shape.instances entry old)
    · exact instanceShape
  · exact allocated.canonicalTypes
  · have bound := allocated.objectLimit
    unfold objectCount at bound
    dsimp only
    omega
  · dsimp only
    rw [retained.limits, instanceCount]
    omega
  · dsimp only
    simp [instances, counted, shape.instanceAccounting, charged]
  · exact limited
  · exact allocated.signatureAccounting
  · exact allocated.signatureLimit
  · exact allocated.memoryAccounting
  · exact allocated.memoryLimit
  · exact allocated.tableAccounting
  · exact allocated.tableLimit

end Itasca.Runtime.Store

end

/-! ## ItemErrors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
theorem item_counts_loop_errors (counts : Array Usize 7#usize) (items start : Usize)
    (startBound : start.val ≤ counts.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop0 items (.Ok ()) counts start
      ⦃ out => ErrorAllowed ResourceError out.2 ∧ (out.2 = .Ok () → out.1.val = items.val + ((counts.val.drop start.val).map UScalar.val).sum) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop0
  apply loop.spec_decr_nat (fun state => counts.val.length - state.2.2.val)
    (fun state => ErrorAllowed ResourceError state.2.1 ∧ state.2.2.val ≤ counts.val.length ∧
      (state.2.1 = .Ok () → state.1.val + ((counts.val.drop state.2.2.val).map UScalar.val).sum =
        items.val + ((counts.val.drop start.val).map UScalar.val).sum))
  · rintro ⟨current, status, index⟩ ⟨errors, bound, total⟩
    dsimp only at errors bound total ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop0.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have hmore : index.val < counts.val.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, errors]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨additional, read⟩
        step with add_items_effect current additional as ⟨status, updated, effect⟩
        have nextErrors : ErrorAllowed ResourceError status := by
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [ok]; trivial
          · rw [failed]; trivial
        have max := counts.property
        step as ⟨next, increment⟩
        refine ⟨nextErrors, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [List.drop_eq_getElem_cons hmore] at exactTotal
            simp only [List.map_cons, List.sum_cons] at exactTotal
            simp only [increment]
            rw [read] at addition
            omega
          · simp [failed] at success
        · omega
    · have equal : index.val = counts.val.length := by simp at *; omega
      simp only [WP.spec_ok]
      refine ⟨errors, ?_⟩
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨True.intro, startBound, fun _ => rfl⟩

theorem element_items_loop_errors (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (startBound : start.val ≤ module.module.env.elements.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop1 module items (.Ok ()) start
      ⦃ out => ErrorAllowed ResourceError out.2 ∧ (out.2 = .Ok () → out.1.val = items.val +
        ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop1
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length - state.2.2.val)
    (fun state => ErrorAllowed ResourceError state.2.1 ∧ state.2.2.val ≤ module.module.env.elements.val.length ∧
      (state.2.1 = .Ok () → state.1.val +
        ((module.module.env.elements.val.drop state.2.2.val).map fun element => element.init.length).sum =
        items.val + ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum))
  · rintro ⟨current, status, index⟩ ⟨errors, bound, total⟩
    dsimp only at errors bound total ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop1.body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have hmore : index.val < module.module.env.elements.val.length := by simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, errors]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨element, read⟩
        step with add_items_effect current element.init.len as ⟨status, updated, effect⟩
        have nextErrors : ErrorAllowed ResourceError status := by
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [ok]; trivial
          · rw [failed]; trivial
        have max := module.module.env.elements.property
        step as ⟨next, increment⟩
        refine ⟨nextErrors, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [List.drop_eq_getElem_cons hmore] at exactTotal
            simp only [List.map_cons, List.sum_cons] at exactTotal
            simp only [increment]
            rw [read] at addition
            simp [alloc.vec.Vec.deref] at addition
            change updated.val = current.val + module.module.env.elements.val[index.val].init.length at addition
            omega
          · simp [failed] at success
        · omega
    · rename_i stop
      have equal : index.val = module.module.env.elements.val.length := by simp [alloc.vec.Vec.deref] at stop; omega
      simp only [WP.spec_ok]
      refine ⟨errors, ?_⟩
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨True.intro, startBound, fun _ => rfl⟩


end Itasca.Runtime.Store

end

/-! ## SourceAllocationLists -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

private theorem maps_two {α β γ δ : Type} (values : List α) (f : α → β) (g : α → γ) (pair : β → γ → δ) :
    Map₂ pair (values.map f) (values.map g) = values.map (fun x => pair (f x) (g x)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simpa only [Map₂, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (pair (f head) (g head) :: ·) ih

private theorem maps_three {α β γ δ ε : Type} (values : List α) (f : α → β) (g : α → γ) (h : α → δ)
    (triple : β → γ → δ → ε) :
    Map₃ triple (values.map f) (values.map g) (values.map h) = values.map (fun x => triple (f x) (g x) (h x)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simpa only [Map₃, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (triple (f head) (g head) (h head) :: ·) ih

theorem GlobalSourceValues.types {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    (values.map decodeGlobal).map globalinst.TYPE = sources.map (fun original => Translate.globalType original.gtype) := by
  induction related with
  | nil => rfl
  | cons current rest ih => simp only [List.map_cons, decode_global_type_source, current.1, ih]

theorem GlobalSourceValues.evaluations {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [value])
      (sources.map fun original => ModuleConstants.expression original.init)
      ((values.map decodeGlobal).map globalinst.VALUE) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih => exact .cons current.2 ih

theorem GlobalSourceValues.syntax {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    sources.map ModuleConstants.global = Map₂ (fun expression ty => global.GLOBAL ty expression)
      (sources.map fun original => ModuleConstants.expression original.init)
      ((values.map decodeGlobal).map globalinst.TYPE) := by
  rw [related.types, maps_two]
  rfl

theorem ElementSourceSegments.types {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    (values.map decodeElement).map eleminst.TYPE = sources.map (fun original => Translate.referenceType original.elem) := by
  induction related with
  | nil => rfl
  | cons current rest ih => simp only [List.map_cons, decodeElement, decode_elem_type_source, current.1, ih]

theorem ElementSourceValues.evaluations {s inst ty sources values}
    (related : ElementSourceValues s inst ty sources values) :
    List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [val_ref value])
      (sources.map ModuleConstants.expression) (values.map (decodeRef ty)) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih =>
    apply List.Forall₂.cons _ ih
    simpa only [ref_val_eq] using current

theorem ElementSourceSegments.evaluations {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    List.Forall₂ (fun expressions references => List.Forall₂
      (fun expression reference => Eval_expr ⟨s, ⟨[], inst⟩⟩ expression ⟨s, ⟨[], inst⟩⟩ [val_ref reference])
      expressions references)
      (sources.map fun original => original.init.val.map ModuleConstants.expression)
      ((values.map decodeElement).map eleminst.REFS) := by
  induction related with
  | nil => exact .nil
  | cons current rest ih =>
    apply List.Forall₂.cons _ ih
    simpa only [decodeElement, current.1] using current.2.evaluations

theorem ElementSourceSegments.syntax {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    (sources.map ModuleEnv.rawElement).map ModuleElaboration.element =
      Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
        (sources.map fun original => ModuleSegments.elementMode original.mode)
        (sources.map fun original => original.init.val.map ModuleConstants.expression)
        ((values.map decodeElement).map eleminst.TYPE) := by
  rw [related.types, maps_three]
  simp only [List.map_map, Function.comp_def, ModuleElaboration.element, ModuleEnv.rawElement]

theorem source_data_payload_syntax (sources : List Itasca.metadata.Data) :
    (sources.map ModuleData.raw).map ModuleData.translate =
      Map₂ data.DATA ((sources.map sourceDataPayload).map datainst.BYTES)
        (sources.map fun original => ModuleSegments.dataMode original.mode) := by
  simp only [List.map_map, Function.comp_def, sourceDataPayload]
  rw [maps_two]
  rfl
end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem GlobalSourceValues.raw_evaluations {s inst sources values}
    (related : GlobalSourceValues s inst sources values) :
    List.Forall₂ (fun original value => Eval_expr ⟨s, ⟨[], inst⟩⟩
      (ModuleConstants.expression original.init) ⟨s, ⟨[], inst⟩⟩ [value])
      sources ((values.map decodeGlobal).map globalinst.VALUE) :=
  List.forall₂_map_left_iff.mp related.evaluations

theorem ElementSourceSegments.raw_evaluations {s inst sources values}
    (related : ElementSourceSegments s inst sources values) :
    List.Forall₂ (fun original references => List.Forall₂
      (fun expression reference => Eval_expr ⟨s, ⟨[], inst⟩⟩ (ModuleConstants.expression expression)
        ⟨s, ⟨[], inst⟩⟩ [val_ref reference]) original.init references)
      (sources.map ModuleEnv.rawElement) ((values.map decodeElement).map eleminst.REFS) := by
  apply List.forall₂_map_left_iff.mpr
  exact (List.forall₂_map_left_iff.mp related.evaluations).imp
    (fun _ _ current => List.forall₂_map_left_iff.mp current)
end Itasca.Runtime.Store

end
