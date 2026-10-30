import Itasca.Runtime.Store.Invariant.FunctionSignatures
import Itasca.Runtime.Store.Invariant.TypeStaging
import Itasca.Runtime.Store.Preparation.PreparationInputs

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
