import Itasca.Runtime.Store.Instantiation.LinkedPreparedRun
import Itasca.Runtime.Store.Invariant.NormalResult
import Itasca.Runtime.Store.Linking.LinkLoop
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Instantiation.PublishInstance
import Itasca.Runtime.Store.Invariant.InvalidWrite
import Itasca.Runtime.Platform.Alloc
import Itasca.Runtime.Store.Invariant.InstanceItems
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.ElementEffects
import Itasca.Runtime.Store.Initialization.DataStagingLoop
import Itasca.Runtime.Store.Initialization.InitializerCertificates
import Itasca.Runtime.Store.Invariant.ItemErrors
import Itasca.Runtime.Store.Linking.LinkErrors
import Itasca.Runtime.Store.Preparation.PreparationErrorLoops
import Itasca.Runtime.Store.Invariant.ObjectAllocationErrors
import Itasca.Runtime.Store.Api.GlobalErrorLoop
import Itasca.Runtime.Store.Initialization.ElementErrorLoop
import Itasca.Runtime.Store.Initialization.DataErrorLoop
import Itasca.Runtime.Store.Initialization.PrecheckCertifiedWitness
import Itasca.Runtime.Store.Instantiation.PrecommitOrigins

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

private theorem deref_len {T : Type} (values : alloc.vec.Vec T) : values.deref.len = values.len := by
  apply UScalar.eq_of_val_eq
  simp [alloc.vec.Vec.deref]

private theorem below_limit (n limit : Usize) (below : ¬n ≥ limit) : n.val < Usize.max := by
  scalar_tac

private theorem below_actual_limit (n limit : Usize) (below : ¬n ≥ limit) : n.val < limit.val := by scalar_tac

private theorem usize_limit (limit : Usize) : limit.val ≤ Usize.max := by scalar_tac

private theorem index_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given values index value found)
  subst actual
  exact read

private theorem set_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) : values.set index value = values := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  rw [← same]
  exact vec_set_current values index bound

private theorem index_mut_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) values index =
      .ok (value, values.set index) := by
  rw [alloc.vec.Vec.index_mut_slice_index]
  unfold alloc.vec.Vec.index_mut_usize
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given values index value found)
  subst actual
  rw [read, bind_tc_ok]

/-- Every actual preparation either returns an ordinary precommit rejection
retaining the old store prefix, or a staged instance whose item charge yields a
fully shaped store. This classification imposes no normal-return or
termination premise on the computation. -/
theorem prepare_instance_classified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env module.profile)
    (dataValid : ∀ data ∈ module.module.tail.data.val, Itasca.ModuleData.Valid module.module.env data)
    (compiled : Compiler.InitializerMappings module)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (outcome : Result (core.result.Result (runtime.InstanceAddr × Usize) runtime.ExecError × runtime.store.Store M × P))
    (run : runtime.store.instantiate.Store.prepare_instance memory hooks floats allocator before module imports platform = outcome) :
    (∃ error staged, outcome = .ok (.Err error, staged, platform) ∧ StagedPrefix before staged ∧ PrecommitError module.profile error ∧ PrecommitOrigins memory view before staged module imports error) ∨
    ∃ staged items charged ready inst, staged.instance_items + items = .ok charged ∧
      ready = {staged with instance_items := charged} ∧
      Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      outcome = .ok (.Ok (⟨before.id, before.instances.len⟩, items), staged, platform) := by
  have tableLimits : ∀ ty ∈ module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX := by
    intro ty member
    have canonical := valid.tables ty member
    refine ⟨by simpa [core.num.U32.MAX, U32.rMax] using canonical.1, ?_⟩
    cases maximum : ty.limits.max with
    | none => trivial
    | some high => simpa [maximum, core.num.U32.MAX, U32.rMax] using canonical.2 high (by simp [maximum])
  have memoryLimits : ∀ ty ∈ module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32 := by
    intro ty member
    have canonical := valid.memories ty member
    refine ⟨by simpa using canonical.1, ?_⟩
    cases maximum : ty.limits.max with
    | none => trivial
    | some high => simpa [maximum] using canonical.2 high (by simp [maximum])
  unfold runtime.store.instantiate.Store.prepare_instance at run
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.imports, bind_ok, ] at run
  split at run
  · rename_i mismatch
    exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by
      constructor
      · intro trap impossible; cases impossible
      · intro link equal
        cases equal
        left
        refine ⟨rfl, ?_⟩
        intro lengths
        have same : imports.len = module.module.env.imports.deref.len := by
          apply UScalar.eq_of_val_eq
          simpa [alloc.vec.Vec.deref] using lengths
        simp [same] at mismatch
      · intro trap impossible; cases impossible⟩
  · rename_i importCount
    split at run
    · exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
    · rename_i instanceSpace
      simp only [Itasca.metadata.Env.impl.types, Itasca.metadata.Env.impl.func_types, Itasca.metadata.Env.impl.table_types, Itasca.metadata.Env.impl.mem_types, Itasca.metadata.Env.impl.global_types, Itasca.metadata.Env.impl.elements,
        runtime.compiler.ExecutableModule.tail, Itasca.metadata.Module.impl.tail,
        bind_ok, deref_len] at run
      obtain ⟨counted, countsRun, countsErrors, countsPost⟩ := WP.spec_imp_exists
        (item_counts_loop_errors (moduleItemCounts module) 0#usize 0#usize (by simp))
      rcases counted with ⟨items, status⟩
      unfold moduleItemCounts at countsRun
      rw [countsRun] at run
      simp only [bind_ok, uncurry_apply_pair] at run
      cases status with
      | Err error =>
        rw [element_items_error] at run
        simp only [bind_ok, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, uncurry_apply_pair] at run
        change Result.ok (.Err error, before, platform) = outcome at run
        exact Or.inl ⟨_, _, run.symm, .refl _, by exact ResourceError.precommit countsErrors, by exact PrecommitOrigins.resource countsErrors⟩
      | Ok value =>
        cases value
        obtain ⟨counted, elementRun, itemErrors, elementPost⟩ := WP.spec_imp_exists
          (element_items_loop_errors module items 0#usize (by simp))
        rcases counted with ⟨total, status⟩
        rw [elementRun] at run
        simp only [bind_ok, uncurry_apply_pair] at run
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
          change Result.ok (.Err error, before, platform) = outcome at run
          exact Or.inl ⟨_, _, run.symm, .refl _, by exact ResourceError.precommit itemErrors, by exact PrecommitOrigins.resource itemErrors⟩
        | Ok value =>
          cases value
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, ] at run
          obtain ⟨fits, fitsRun, fitsPost⟩ := WP.spec_imp_exists (within_spec before.instance_items total before.limits.max_instance_items)
          rw [fitsRun] at run
          simp only [bind_ok, ] at run
          cases fits with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at run
            exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
          | true =>
            simp only [↓reduceIte] at run
            have exactItems : total.val = moduleItems module := by
              have elements := elementPost rfl
              have counts := countsPost rfl
              simpa [moduleItemCounts, moduleItems, counts, Array.make, Nat.add_assoc] using elements
            have itemFits : before.instance_items.val + total.val ≤ before.limits.max_instance_items.val := by
              simpa using fitsPost.symm
            obtain ⟨elementCapacity, dataCapacity, globalLength, elementLength, dataLength⟩ :=
              instance_segment_capacity before module shape accounted total exactItems itemFits
            have importLengths : imports.length = module.module.env.imports.length := by
              change imports.val.length = module.module.env.imports.val.length
              simpa [alloc.vec.Vec.deref] using importCount
            obtain ⟨funcsReserved, funcsRun⟩ := reserve_wrapper_eq allocator law
              (alloc.vec.Vec.new runtime.FuncAddr) module.module.env.func_types.len
            rw [funcsRun] at run
            simp only [bind_ok, uncurry_apply_pair] at run
            cases funcsReserved with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, 
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
              change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                outcome at run
              exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
            | true =>
              simp only [↓reduceIte, bind_ok] at run
              obtain ⟨tablesReserved, tablesRun⟩ := reserve_wrapper_eq allocator law
                (alloc.vec.Vec.new runtime.TableAddr) module.module.env.table_types.len
              rw [tablesRun] at run
              simp only [bind_ok, uncurry_apply_pair] at run
              cases tablesReserved with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, 
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                  outcome at run
                exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
              | true =>
                simp only [↓reduceIte, bind_ok] at run
                obtain ⟨memoriesReserved, memoriesRun⟩ := reserve_wrapper_eq allocator law
                  (alloc.vec.Vec.new runtime.MemoryAddr) module.module.env.mem_types.len
                rw [memoriesRun] at run
                simp only [bind_ok, uncurry_apply_pair] at run
                cases memoriesReserved with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, 
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                  change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                    outcome at run
                  exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                | true =>
                  simp only [↓reduceIte, bind_ok] at run
                  obtain ⟨globalsReserved, globalsRun⟩ := reserve_wrapper_eq allocator law
                    (alloc.vec.Vec.new runtime.GlobalAddr) module.module.env.global_types.len
                  rw [globalsRun] at run
                  simp only [bind_ok, uncurry_apply_pair] at run
                  cases globalsReserved with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte, 
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                    change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                      outcome at run
                    exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                  | true =>
                    simp only [↓reduceIte, bind_ok] at run
                    let seed : runtime.store.ModuleInst := {
                      module := module, types := alloc.vec.Vec.new Usize,
                      funcs := alloc.vec.Vec.new runtime.FuncAddr, tables := alloc.vec.Vec.new runtime.TableAddr,
                      memories := alloc.vec.Vec.new runtime.MemoryAddr, globals := alloc.vec.Vec.new runtime.GlobalAddr,
                      elems := alloc.vec.Vec.new Usize, datas := alloc.vec.Vec.new Usize }
                    have seedMaps : LinkedMaps view before module (module.module.env.imports.val.take 0) seed := by
                      simpa using linked_maps_empty view before seed rfl rfl rfl rfl rfl rfl rfl
                    obtain ⟨⟨linkedStore, linkStatus, inst⟩, linkedRun, sameStore, source, linked⟩ := WP.spec_imp_exists
                      (link_imports_loop memory view laws before shape module imports importLengths handles cache
                        seed 0#usize (by simp) seedMaps)
                    dsimp only at sameStore source linked
                    subst linkedStore
                    rw [linkedRun] at run
                    simp only [bind_ok, uncurry_apply_pair] at run
                    cases linkStatus with
                    | Err error =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                      exact Or.inl ⟨_, _, run.symm, .refl _, by exact link_staging_errors memory module.profile imports before seed 0#usize (.Ok ()) True.intro linkedRun, by exact PrecommitOrigins.linked inst linkedRun (link_staging_errors memory .Wasm2 imports before seed 0#usize (.Ok ()) True.intro linkedRun)⟩
                    | Ok value =>
                      cases value
                      have maps : LinkedMaps view before inst.module inst.module.module.env.imports.val inst := by
                        simpa only [source] using linked rfl
                      have instCache : Cache inst.module.module.env tables memories := by simpa only [source] using cache
                      simp only [bind_ok] at run
                      obtain ⟨typesReserved, typesRun⟩ := reserve_wrapper_eq allocator law inst.types inst.module.module.env.types.len
                      rw [typesRun] at run
                      simp only [bind_ok, uncurry_apply_pair] at run
                      cases typesReserved with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte, 
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                          core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                        exact Or.inl ⟨_, _, run.symm, .refl _, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                      | true =>
                        simp only [↓reduceIte, bind_ok] at run
                        have eta : {inst with types := inst.types} = inst := by cases inst; rfl
                        rw [eta] at run
                        have objectBound : objectCount before ≤ Usize.max := by
                          have bound := shape.objectLimit
                          unfold objectCount
                          scalar_tac
                        have emptyTypes : TypeEntries before (inst.module.module.env.types.val.take 0) inst.types.val := by
                          simp [TypeEntries, maps.types]
                        obtain ⟨out, typedRun, typed, typeInst, status, parts, typeStore, typeMap, typePrefix, typeBound, typeEntries⟩ :=
                          WP.spec_imp_exists (type_staging_loop memory allocator law before before inst inst 0#usize
                            (by simp) rfl rfl (.refl _) objectBound emptyTypes)
                        subst out
                        rw [typedRun] at run
                        simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                        cases status with
                        | Err error =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                          exact Or.inl ⟨_, _, run.symm, typePrefix, by exact ResourceError.precommit (type_staging_errors memory allocator law before inst 0#usize (.Ok ()) True.intro typedRun), by exact PrecommitOrigins.resource (type_staging_errors memory allocator law before inst 0#usize (.Ok ()) True.intro typedRun)⟩
                        | Ok value =>
                          cases value
                          simp only [bind_ok] at run
                          have typeStore_funcs := congrArg runtime.store.Store.funcs typeStore
                          dsimp only at typeStore_funcs
                          have typeStore_tables := congrArg runtime.store.Store.tables typeStore
                          dsimp only at typeStore_tables
                          have typeStore_memories := congrArg runtime.store.Store.memories typeStore
                          dsimp only at typeStore_memories
                          have typeStore_globals := congrArg runtime.store.Store.globals typeStore
                          dsimp only at typeStore_globals
                          have typeStore_instances := congrArg runtime.store.Store.instances typeStore
                          dsimp only at typeStore_instances
                          have typeStore_elems := congrArg runtime.store.Store.elems typeStore
                          dsimp only at typeStore_elems
                          have typeStore_datas := congrArg runtime.store.Store.datas typeStore
                          dsimp only at typeStore_datas
                          have typeMap_module := congrArg runtime.store.ModuleInst.module typeMap
                          dsimp only at typeMap_module
                          have typeMap_tables := congrArg runtime.store.ModuleInst.tables typeMap
                          dsimp only at typeMap_tables
                          have typeMap_memories := congrArg runtime.store.ModuleInst.memories typeMap
                          dsimp only at typeMap_memories
                          have typeMap_globals := congrArg runtime.store.ModuleInst.globals typeMap
                          dsimp only at typeMap_globals
                          have typeMap_elements := congrArg runtime.store.ModuleInst.elems typeMap
                          dsimp only at typeMap_elements
                          have typeMap_data := congrArg runtime.store.ModuleInst.datas typeMap
                          dsimp only at typeMap_data
                          have typeSource : typeInst.module = inst.module := by
                            have h := congrArg runtime.store.ModuleInst.module typeMap
                            exact h
                          have typeFuncs : typeInst.funcs = inst.funcs := by
                            have h := congrArg runtime.store.ModuleInst.funcs typeMap
                            exact h
                          have typesComplete : typeInst.types.length = inst.module.module.env.types.length :=
                            (typeEntries rfl).length_eq.symm
                          have sourceIndices := cache_defined_type_bounds instCache typeInst.types typesComplete
                          have preparedIndices : ∀ idx ∈ typeInst.module.module.env.func_type_indices.val,
                              idx.val < typeInst.types.length := by simpa only [typeSource] using sourceIndices
                          have importedIssued := (maps.bindings shape).funcs
                          have typedIssued : ∀ addr ∈ typeInst.funcs.val, addr.index.val < typed.funcs.length := by
                            simpa only [typeFuncs, typeStore_funcs] using importedIssued
                          have functionCapacity : typeInst.funcs.length + typeInst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
                            simpa only [typeFuncs, typeSource] using maps.function_capacity instCache
                          have functionChecked := function_staging_loop memory allocator law typed typed typeInst typeInst before.instances.len 0#usize
                            (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity
                          obtain ⟨out, functionRun, functions, funcInst, status, parts, functionStore, functionMap,
                              functionPrefix, functionBound, functionIssued, functionCount⟩ := WP.spec_imp_exists functionChecked
                          subst out
                          rw [functionRun] at run
                          simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                          cases status with
                          | Err error =>
                            simp only [
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                              core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                            exact Or.inl ⟨_, _, run.symm, typePrefix.trans functionPrefix, by exact ResourceError.precommit (function_staging_errors memory allocator law typed typeInst before.instances.len 0#usize (.Ok ()) True.intro functionRun), by exact PrecommitOrigins.resource (function_staging_errors memory allocator law typed typeInst before.instances.len 0#usize (.Ok ()) True.intro functionRun)⟩
                          | Ok value =>
                            cases value
                            simp only [bind_ok] at run
                            have functionStore_tables := congrArg runtime.store.Store.tables functionStore
                            dsimp only at functionStore_tables
                            have functionStore_memories := congrArg runtime.store.Store.memories functionStore
                            dsimp only at functionStore_memories
                            have functionStore_globals := congrArg runtime.store.Store.globals functionStore
                            dsimp only at functionStore_globals
                            have functionStore_instances := congrArg runtime.store.Store.instances functionStore
                            dsimp only at functionStore_instances
                            have functionStore_elems := congrArg runtime.store.Store.elems functionStore
                            dsimp only at functionStore_elems
                            have functionStore_datas := congrArg runtime.store.Store.datas functionStore
                            dsimp only at functionStore_datas
                            have functionMap_module := congrArg runtime.store.ModuleInst.module functionMap
                            dsimp only at functionMap_module
                            have functionMap_tables := congrArg runtime.store.ModuleInst.tables functionMap
                            dsimp only at functionMap_tables
                            have functionMap_memories := congrArg runtime.store.ModuleInst.memories functionMap
                            dsimp only at functionMap_memories
                            have functionMap_globals := congrArg runtime.store.ModuleInst.globals functionMap
                            dsimp only at functionMap_globals
                            have functionMap_elements := congrArg runtime.store.ModuleInst.elems functionMap
                            dsimp only at functionMap_elements
                            have functionMap_data := congrArg runtime.store.ModuleInst.datas functionMap
                            dsimp only at functionMap_data
                            have functionSource : funcInst.module = inst.module := by
                              simpa only [functionMap_module] using typeSource
                            obtain ⟨tableStart, importedTables⟩ := maps.table_start instCache
                            have tableStartBound : funcInst.tables.len.val ≤ funcInst.module.module.env.table_types.val.length := by
                              simpa only [alloc.vec.Vec.len_val, functionMap_tables, typeMap_tables, functionMap_module, typeMap_module] using tableStart
                            have tableIssued : ∀ addr ∈ funcInst.tables.val, addr.index.val < functions.tables.length := by
                              simpa only [functionMap_tables, typeMap_tables, functionStore_tables, typeStore_tables] using importedTables
                            have tableChecked := table_staging_loop memory allocator law functions functions funcInst funcInst funcInst.tables.len
                              tableStartBound rfl rfl (.refl _) functionBound tableIssued (by simp)
                            obtain ⟨out, tableRun, tabled, tableInst, status, parts, tableStore, tableMap, tablePrefix, tableBound, tableAddresses, tableCount⟩ := WP.spec_imp_exists tableChecked
                            subst out
                            rw [tableRun] at run
                            simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                            cases status with
                            | Err error =>
                              simp only [
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                              exact Or.inl ⟨_, _, run.symm, typePrefix.trans (functionPrefix.trans tablePrefix), by exact ResourceError.precommit (table_staging_errors memory allocator law functions funcInst funcInst.tables.len (by simpa only [functionSource, source] using tableLimits) (.Ok ()) True.intro tableRun), by exact PrecommitOrigins.resource (table_staging_errors memory allocator law functions funcInst funcInst.tables.len (by simpa only [functionSource, source] using tableLimits) (.Ok ()) True.intro tableRun)⟩
                            | Ok value =>
                              cases value
                              simp only [bind_ok] at run
                              have tableStore_funcs := congrArg runtime.store.Store.funcs tableStore
                              dsimp only at tableStore_funcs
                              have tableStore_memories := congrArg runtime.store.Store.memories tableStore
                              dsimp only at tableStore_memories
                              have tableStore_globals := congrArg runtime.store.Store.globals tableStore
                              dsimp only at tableStore_globals
                              have tableStore_instances := congrArg runtime.store.Store.instances tableStore
                              dsimp only at tableStore_instances
                              have tableStore_elems := congrArg runtime.store.Store.elems tableStore
                              dsimp only at tableStore_elems
                              have tableStore_datas := congrArg runtime.store.Store.datas tableStore
                              dsimp only at tableStore_datas
                              have tableMap_module := congrArg runtime.store.ModuleInst.module tableMap
                              dsimp only at tableMap_module
                              have tableMap_funcs := congrArg runtime.store.ModuleInst.funcs tableMap
                              dsimp only at tableMap_funcs
                              have tableMap_memories := congrArg runtime.store.ModuleInst.memories tableMap
                              dsimp only at tableMap_memories
                              have tableMap_globals := congrArg runtime.store.ModuleInst.globals tableMap
                              dsimp only at tableMap_globals
                              have tableMap_elements := congrArg runtime.store.ModuleInst.elems tableMap
                              dsimp only at tableMap_elements
                              have tableMap_data := congrArg runtime.store.ModuleInst.datas tableMap
                              dsimp only at tableMap_data
                              obtain ⟨memoryStart, importedMemories⟩ := maps.memory_start instCache
                              have memoryStartBound : tableInst.memories.len.val ≤ tableInst.module.module.env.mem_types.val.length := by
                                simpa only [alloc.vec.Vec.len_val, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
                              have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
                                simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
                              have memoryChecked := memory_staging_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
                                memoryStartBound rfl rfl (.refl _) tableBound memoryIssued (by simp)
                              obtain ⟨out, memoryRun, prepared, preparedInst, status, parts, memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAddresses, memoryCount⟩ := WP.spec_imp_exists memoryChecked
                              subst out
                              rw [memoryRun] at run
                              simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                              cases status with
                              | Err error =>
                                simp only [
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                  core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                exact Or.inl ⟨_, _, run.symm, typePrefix.trans (functionPrefix.trans (tablePrefix.trans memoryPrefix)), by exact ResourceError.precommit (memory_staging_errors memory allocator law view laws tabled tableInst tableInst.memories.len (by simpa only [tableMap_module, functionSource, source] using memoryLimits) (.Ok ()) True.intro memoryRun), by exact PrecommitOrigins.resource (memory_staging_errors memory allocator law view laws tabled tableInst tableInst.memories.len (by simpa only [tableMap_module, functionSource, source] using memoryLimits) (.Ok ()) True.intro memoryRun)⟩
                              | Ok value =>
                                cases value
                                have preparedFacts := preparation_success memory allocator law view laws before inst shape maps instCache
                                  before.instances.len typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                  typedRun functionRun tableRun memoryRun
                                obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
                                  preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
                                  preparedBindings, preparedImports, preparedSegments⟩ := preparedFacts
                                simp only [bind_ok] at run
                                obtain ⟨instancesReserved, instancesRun⟩ := reserve_wrapper_eq allocator law prepared.instances 1#usize
                                rw [instancesRun] at run
                                simp only [bind_ok, uncurry_apply_pair] at run
                                cases instancesReserved with
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte, 
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                    core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                  exact Or.inl ⟨_, _, run.symm, preparedPrefix, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                                | true =>
                                  simp only [↓reduceIte, bind_ok] at run
                                  have instanceRoom : prepared.instances.length < Usize.max := by
                                    rw [preparedInstances]
                                    exact below_limit before.instances.len before.limits.max_instances instanceSpace
                                  have preparedAccounting : SegmentAccounting prepared := by
                                    constructor
                                    · simpa only [preparedElements, preparedInstances] using accounted.elements
                                    · simpa only [preparedData, preparedInstances] using accounted.datas
                                  have emptyElements : preparedInst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
                                  have emptyData : preparedInst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
                                  obtain ⟨publishedInstances, publishedRun, appended, publishedFound, publishedPrefix,
                                    publishedBindings, publishedImports, publishedSegments, publishedAccounting, publishedObjects⟩ :=
                                    WP.spec_imp_exists (publish_prepared_instance prepared preparedInst instanceRoom preparedBindings
                                      preparedImports preparedSegments preparedAccounting emptyElements emptyData)
                                  rw [publishedRun] at run
                                  simp only [bind_ok] at run
                                  let published := {prepared with instances := publishedInstances}
                                  have indexFound : published.instances.val[before.instances.len.val]? = some preparedInst := by
                                    simpa only [preparedInstances] using publishedFound
                                  have publishedBound : objectCount published ≤ Usize.max := by
                                    change objectCount {prepared with instances := publishedInstances} ≤ Usize.max
                                    rw [publishedObjects]
                                    exact preparedBound
                                  have globalValid : ∀ global ∈ preparedInst.module.module.env.globals.val,
                                      Itasca.ModuleConstants.Valid preparedInst.module.module.env global.init global.gtype.valtype := by
                                    simpa only [preparedSource, source] using valid.globals
                                  have globalCapacity : preparedInst.globals.length + (preparedInst.module.module.env.globals.val.length - 0) ≤ Usize.max := by
                                    simpa only [preparedGlobalMap, preparedSource, Nat.sub_zero] using maps.global_capacity instCache
                                  have publishedCompiled : Compiler.InitializerMappings preparedInst.module := by simpa only [preparedSource, source] using compiled
                                  obtain ⟨out, globalRun, globalStore, globalStatus, parts, globalErrors, globalPrefix, globalBound,
                                    globalAccounting, globalMetadata, globalInst, globalFound, globalSource, globalBindings, globalImports,
                                    globalSegments, globalElements, globalData, globalElementMap, globalDataMap⟩ := WP.spec_imp_exists
                                    (global_staging_loop_errors memory hooks floats allocator law before published platform before.instances.len 0#usize
                                      preparedInst (.Ok ()) True.intro (preparedPrefix.trans publishedPrefix) (by simp) indexFound publishedCompiled
                                      globalValid publishedBindings publishedImports publishedSegments publishedBound (by simp) globalCapacity)
                                  subst out
                                  rw [globalRun] at run
                                  simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                  cases globalStatus with
                                  | Err error =>
                                    simp only [
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                    exact Or.inl ⟨_, _, run.symm, globalPrefix, by exact ResourceError.precommit globalErrors, by exact PrecommitOrigins.resource globalErrors⟩
                                  | Ok value =>
                                    cases value
                                    simp only [bind_ok] at run
                                    rw [index_given globalStore.instances before.instances.len globalInst globalFound, bind_ok] at run
                                    rw [index_mut_given globalStore.instances before.instances.len globalInst globalFound, bind_ok] at run
                                    simp only [uncurry_apply_pair] at run
                                    obtain ⟨elementsReserved, elementsRun⟩ := reserve_wrapper_eq allocator law globalInst.elems globalInst.module.module.env.elements.len
                                    rw [elementsRun] at run
                                    simp only [bind_ok, uncurry_apply_pair] at run
                                    have elementEta : {globalInst with elems := globalInst.elems} = globalInst := by cases globalInst; rfl
                                    simp only [set_given globalStore.instances before.instances.len globalInst globalFound] at run
                                    cases elementsReserved with
                                    | false =>
                                      simp only [Bool.false_eq_true, ↓reduceIte, 
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                        core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                      exact Or.inl ⟨_, _, run.symm, globalPrefix, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                                    | true =>
                                      simp only [↓reduceIte, bind_ok] at run
                                      have globalCompiled : Compiler.InitializerMappings globalInst.module := by
                                        simpa only [globalSource] using publishedCompiled
                                      have elementValid : ∀ segment ∈ globalInst.module.module.env.elements.val,
                                          Itasca.ModuleSegments.elementValid globalInst.module.module.env segment := by
                                        simpa only [globalSource, preparedSource, source] using valid.elements
                                      have elementStoreCapacity : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
                                        simpa only [globalElements, published, preparedElements, globalSource, preparedSource, source, Nat.sub_zero] using elementCapacity
                                      have elementMapCapacity : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
                                        have empty : globalInst.elems.val = [] := by rw [globalElementMap]; exact emptyElements
                                        simpa only [alloc.vec.Vec.length, empty, List.length_nil, Nat.zero_add, globalSource,
                                          preparedSource, source, Nat.sub_zero] using elementLength
                                      obtain ⟨out, elementStageRun, elementStore, elementStatus, parts, elementErrors, elementPrefix, elementBound,
                                        elementAccounting, elementMetadata, elementInst, elementFound, elementSource, elementBindings, elementImports,
                                        elementSegments, elementData, elementDataMap⟩ := WP.spec_imp_exists
                                        (element_staging_loop_errors memory hooks floats allocator law before globalStore platform before.instances.len 0#usize
                                          globalInst (.Ok ()) True.intro globalPrefix (by simp) globalFound globalCompiled elementValid globalBindings globalImports
                                          globalSegments globalBound (by simp) elementStoreCapacity elementMapCapacity)
                                      subst out
                                      rw [elementStageRun] at run
                                      simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                      cases elementStatus with
                                      | Err error =>
                                        simp only [
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                          core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                        exact Or.inl ⟨_, _, run.symm, elementPrefix, by exact ResourceError.precommit elementErrors, by exact PrecommitOrigins.resource elementErrors⟩
                                      | Ok value =>
                                        cases value
                                        simp only [bind_ok] at run
                                        rw [index_given elementStore.instances before.instances.len elementInst elementFound, bind_ok] at run
                                        rw [index_mut_given elementStore.instances before.instances.len elementInst elementFound, bind_ok] at run
                                        simp only [uncurry_apply_pair] at run
                                        obtain ⟨dataReserved, dataRun⟩ := reserve_wrapper_eq allocator law elementInst.datas elementInst.module.module.tail.data.len
                                        rw [dataRun] at run
                                        simp only [bind_ok, uncurry_apply_pair] at run
                                        have dataEta : {elementInst with datas := elementInst.datas} = elementInst := by cases elementInst; rfl
                                        simp only [set_given elementStore.instances before.instances.len elementInst elementFound] at run
                                        cases dataReserved with
                                        | false =>
                                          simp only [Bool.false_eq_true, ↓reduceIte, 
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                          exact Or.inl ⟨_, _, run.symm, elementPrefix, by trivial, by exact PrecommitOrigins.resource True.intro⟩
                                        | true =>
                                          simp only [↓reduceIte, bind_ok] at run
                                          have dataStoreCapacity : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
                                            simpa only [elementData, globalData, published, preparedData, elementSource, globalSource,
                                              preparedSource, source, Nat.sub_zero] using dataCapacity
                                          have dataMapCapacity : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
                                            have empty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap]; exact emptyData
                                            simpa only [alloc.vec.Vec.length, empty, List.length_nil, Nat.zero_add, elementSource, globalSource,
                                              preparedSource, source, Nat.sub_zero] using dataLength
                                          obtain ⟨out, dataStageRun, dataStore, dataStatus, parts, dataPrefix, dataBound, dataAccounting, dataMetadata,
                                            dataInst, dataFound, dataSource, dataBindings, dataImports, dataSegments⟩ := WP.spec_imp_exists
                                            (data_staging_loop memory allocator law before elementStore before.instances.len 0#usize elementInst (.Ok ())
                                              elementPrefix (by simp) elementFound elementBindings elementImports elementSegments elementBound
                                              (by simp) dataStoreCapacity dataMapCapacity)
                                          subst out
                                          rw [dataStageRun] at run
                                          simp only [storeStateParts, bind_ok, uncurry_apply_pair] at run
                                          cases dataStatus with
                                          | Err error =>
                                            simp only [
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                              core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                            exact Or.inl ⟨_, _, run.symm, dataPrefix, by exact ResourceError.precommit (data_staging_errors memory allocator law elementStore before.instances.len 0#usize (.Ok ()) True.intro dataStore (.Err error) dataStageRun), by exact PrecommitOrigins.resource (data_staging_errors memory allocator law elementStore before.instances.len 0#usize (.Ok ()) True.intro dataStore (.Err error) dataStageRun)⟩
                                          | Ok value =>
                                            cases value
                                            simp only [bind_ok] at run
                                            rw [index_given dataStore.instances before.instances.len dataInst dataFound, bind_ok] at run
                                            simp only [runtime.compiler.ExecutableModule.impl.profile, bind_ok] at run
                                            have finalSource : dataInst.module = module :=
                                              dataSource.trans (elementSource.trans (globalSource.trans (preparedSource.trans source)))
                                            have finalCompiled : Compiler.InitializerMappings dataInst.module := by simpa only [finalSource] using compiled
                                            have finalElements : ∀ segment ∈ dataInst.module.module.env.elements.val,
                                                Itasca.ModuleSegments.elementValid dataInst.module.module.env segment := by
                                              simpa only [finalSource] using valid.elements
                                            have finalData : ∀ segment ∈ dataInst.module.module.tail.data.val,
                                                Itasca.ModuleData.Valid dataInst.module.module.env segment := by
                                              simpa only [finalSource] using dataValid
                                            cases profile : dataInst.module.profile with
                                            | Wasm2 =>
                                              simp only [runtime.store.wasm1, profile, bind_ok, Bool.false_eq_true, ↓reduceIte] at run
                                              have chargeBound : dataStore.instance_items.val + total.val ≤ Usize.max := by
                                                rw [dataPrefix.instanceItems]
                                                exact itemFits.trans (usize_limit _)
                                              obtain ⟨charged, chargeRun, chargeSpec⟩ := WP.spec_imp_exists
                                                (Usize.add_spec (x := dataStore.instance_items) (y := total) chargeBound)
                                              have counted : charged.val = before.instance_items.val + moduleItems inst.module := by
                                                simpa only [dataPrefix.instanceItems, exactItems, source] using chargeSpec
                                              have limited : charged.val ≤ before.limits.max_instance_items.val := by
                                                rw [chargeSpec, dataPrefix.instanceItems]
                                                exact itemFits
                                              have actualRoom : before.instances.length < before.limits.max_instances.val := by
                                                simpa only [alloc.vec.Vec.len_val] using below_actual_limit _ _ instanceSpace
                                              obtain ⟨next, nextFound, nextSource, readyShape, typeBindings, retained, segmentsAccounted, readyCode⟩ :=
                                                prepared_commit_shape memory hooks floats allocator law view laws before inst platform shape accounted maps instCache
                                                  (by simpa only [source] using valid) (by simpa only [source] using compiled) actualRoom
                                                  (by simpa only [source] using elementCapacity) (by simpa only [source] using dataCapacity)
                                                  charged counted limited typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                                  typedRun functionRun tableRun memoryRun publishedInstances publishedRun
                                                  globalStore elementStore dataStore globalRun elementStageRun dataStageRun
                                              let ready := {dataStore with instance_items := charged}
                                              refine Or.inr ⟨dataStore, total, charged, ready, next, chargeRun, rfl, readyShape, nextFound, nextSource.trans source, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                              · have same : next = dataInst := Option.some.inj (nextFound.symm.trans dataFound)
                                                subst next
                                                exact ⟨dataImports.funcs, dataImports.globals⟩
                                              · exact ⟨typeBindings.tables, typeBindings.elements⟩
                                              · exact ⟨segmentsAccounted.elements, segmentsAccounted.datas⟩
                                              · exact readyCode
                                              · exact ⟨{
                                                  seed := inst, source := source, maps := maps, instanceRoom := actualRoom,
                                                  importsLength := importLengths, linkRun := linkedRun,
                                                  elementCapacity := by simpa only [source] using elementCapacity,
                                                  dataCapacity := by simpa only [source] using dataCapacity,
                                                  typed := typed, functions := functions, tabled := tabled, prepared := prepared,
                                                  typeInst := typeInst, funcInst := funcInst, tableInst := tableInst, inst := preparedInst,
                                                  typeRun := typedRun, functionRun := functionRun, tableRun := tableRun, memoryRun := memoryRun,
                                                  publishedInstances := publishedInstances, publicationRun := publishedRun,
                                                  globalStore := globalStore, elementStore := elementStore, dataStore := dataStore,
                                                  globalRun := globalRun, elementRun := elementStageRun, dataRun := dataStageRun,
                                                  charged := charged, counted := counted, limited := limited, committed := rfl }⟩
                                              · exact run.symm
                                            | Wasm1 =>
                                              simp only [runtime.store.wasm1, profile, bind_ok, ↓reduceIte] at run
                                              have chargeBound : dataStore.instance_items.val + total.val ≤ Usize.max := by
                                                rw [dataPrefix.instanceItems]
                                                exact itemFits.trans (usize_limit _)
                                              obtain ⟨ghostCharge, ghostChargeRun, ghostChargeSpec⟩ := WP.spec_imp_exists
                                                (Usize.add_spec (x := dataStore.instance_items) (y := total) chargeBound)
                                              have ghostCounted : ghostCharge.val = before.instance_items.val + moduleItems inst.module := by
                                                simpa only [dataPrefix.instanceItems, exactItems, source] using ghostChargeSpec
                                              have ghostLimited : ghostCharge.val ≤ before.limits.max_instance_items.val := by
                                                rw [ghostChargeSpec, dataPrefix.instanceItems]
                                                exact itemFits
                                              have actualRoom : before.instances.length < before.limits.max_instances.val := by
                                                simpa only [alloc.vec.Vec.len_val] using below_actual_limit _ _ instanceSpace
                                              obtain ⟨ghostInst, ghostFound, ghostSource, ghostShape, ghostTypes, ghostRetained, ghostSegments, ghostCode⟩ :=
                                                prepared_commit_shape memory hooks floats allocator law view laws before inst platform shape accounted maps instCache
                                                  (by simpa only [source] using valid) (by simpa only [source] using compiled) actualRoom
                                                  (by simpa only [source] using elementCapacity) (by simpa only [source] using dataCapacity)
                                                  ghostCharge ghostCounted ghostLimited typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                                  typedRun functionRun tableRun memoryRun publishedInstances publishedRun
                                                  globalStore elementStore dataStore globalRun elementStageRun dataStageRun
                                              have finalCount : dataStore.instances.length = before.instances.length + 1 := by
                                                rw [(dataMetadata.resolve dataFound).instanceCount,
                                                  (elementMetadata.resolve elementFound).instanceCount,
                                                  (globalMetadata.resolve globalFound).instanceCount]
                                                simp only [published, alloc.vec.Vec.length, appended, List.length_append,
                                                  List.length_singleton, preparedInstances]
                                              have stageEvidence (error : runtime.ExecError) (cause : PrecheckCause view dataStore dataInst error) :
                                                  PrecommitStageEvidence view before dataStore module error := by
                                                intro trap equal
                                                exact ⟨ghostCharge, dataInst, ghostShape, finalCount, dataFound, finalSource, cause⟩
                                              obtain ⟨out, elementCheckRun, elementCheckStatus, parts, elementCheckErrors⟩ := WP.spec_imp_exists
                                                (element_precheck_certified_witness memory hooks floats allocator law view dataStore platform before.instances.len
                                                  dataInst (.Ok ()) True.intro dataFound finalCompiled finalElements dataBindings dataImports dataSegments)
                                              subst out
                                              rw [elementCheckRun] at run
                                              simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                              cases elementCheckStatus with
                                              | Err error =>
                                                simp only [
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                                  core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                                exact Or.inl ⟨_, _, run.symm, dataPrefix, by simpa only [ErrorAllowed, ← finalSource, profile] using (PrecheckCause.precommit elementCheckErrors), by exact PrecommitOrigins.precheck before.instances.len dataInst dataFound finalSource elementCheckErrors (stageEvidence _ elementCheckErrors)⟩
                                              | Ok value =>
                                                cases value
                                                simp only [bind_ok] at run
                                                obtain ⟨out, dataCheckRun, dataCheckStatus, parts, dataCheckErrors⟩ := WP.spec_imp_exists
                                                  (data_precheck_certified_witness memory hooks floats allocator law view laws dataStore platform before.instances.len
                                                    dataInst (.Ok ()) True.intro dataFound finalCompiled finalData dataBindings dataImports dataSegments)
                                                subst out
                                                rw [dataCheckRun] at run
                                                simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                                cases dataCheckStatus with
                                                | Err error =>
                                                  simp only [
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                                    core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                                  exact Or.inl ⟨_, _, run.symm, dataPrefix, by simpa only [ErrorAllowed, ← finalSource, profile] using (PrecheckCause.precommit dataCheckErrors), by exact PrecommitOrigins.precheck before.instances.len dataInst dataFound finalSource dataCheckErrors (stageEvidence _ dataCheckErrors)⟩
                                                | Ok value =>
                                                  cases value
                                                  simp only [bind_ok] at run
                                                  have chargeBound : dataStore.instance_items.val + total.val ≤ Usize.max := by
                                                    rw [dataPrefix.instanceItems]
                                                    exact itemFits.trans (usize_limit _)
                                                  obtain ⟨charged, chargeRun, chargeSpec⟩ := WP.spec_imp_exists
                                                    (Usize.add_spec (x := dataStore.instance_items) (y := total) chargeBound)
                                                  have counted : charged.val = before.instance_items.val + moduleItems inst.module := by
                                                    simpa only [dataPrefix.instanceItems, exactItems, source] using chargeSpec
                                                  have limited : charged.val ≤ before.limits.max_instance_items.val := by
                                                    rw [chargeSpec, dataPrefix.instanceItems]
                                                    exact itemFits
                                                  have actualRoom : before.instances.length < before.limits.max_instances.val := by
                                                    simpa only [alloc.vec.Vec.len_val] using below_actual_limit _ _ instanceSpace
                                                  obtain ⟨next, nextFound, nextSource, readyShape, typeBindings, retained, segmentsAccounted, readyCode⟩ :=
                                                    prepared_commit_shape memory hooks floats allocator law view laws before inst platform shape accounted maps instCache
                                                      (by simpa only [source] using valid) (by simpa only [source] using compiled) actualRoom
                                                      (by simpa only [source] using elementCapacity) (by simpa only [source] using dataCapacity)
                                                      charged counted limited typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                                      typedRun functionRun tableRun memoryRun publishedInstances publishedRun
                                                      globalStore elementStore dataStore globalRun elementStageRun dataStageRun
                                                  let ready := {dataStore with instance_items := charged}
                                                  refine Or.inr ⟨dataStore, total, charged, ready, next, chargeRun, rfl, readyShape, nextFound, nextSource.trans source, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                                  · have same : next = dataInst := Option.some.inj (nextFound.symm.trans dataFound)
                                                    subst next
                                                    exact ⟨dataImports.funcs, dataImports.globals⟩
                                                  · exact ⟨typeBindings.tables, typeBindings.elements⟩
                                                  · exact ⟨segmentsAccounted.elements, segmentsAccounted.datas⟩
                                                  · exact readyCode
                                                  · exact ⟨{
                                                      seed := inst, source := source, maps := maps, instanceRoom := actualRoom,
                                                      importsLength := importLengths, linkRun := linkedRun,
                                                      elementCapacity := by simpa only [source] using elementCapacity,
                                                      dataCapacity := by simpa only [source] using dataCapacity,
                                                      typed := typed, functions := functions, tabled := tabled, prepared := prepared,
                                                      typeInst := typeInst, funcInst := funcInst, tableInst := tableInst, inst := preparedInst,
                                                      typeRun := typedRun, functionRun := functionRun, tableRun := tableRun, memoryRun := memoryRun,
                                                      publishedInstances := publishedInstances, publicationRun := publishedRun,
                                                      globalStore := globalStore, elementStore := elementStore, dataStore := dataStore,
                                                      globalRun := globalRun, elementRun := elementStageRun, dataRun := dataStageRun,
                                                      charged := charged, counted := counted, limited := limited, committed := rfl }⟩
                                                  · exact run.symm

end Itasca.Runtime.Store
