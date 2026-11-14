import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Api.MemoryAllocationLoop
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Preparation.PreparationResults
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Preparation.PreparationCalls
import Itasca.Runtime.Store.Api.DefineTable
import Itasca.Runtime.Store.Initialization.InitializerResourceCauses
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: TableAllocationLoop, TableBindingLoop, GlobalStagingCauses.
-/

/-! ## TableAllocationLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table loop allocates a decoded source suffix in order and issues
consecutive fresh addresses, preserving all previous objects. -/
theorem table_allocation_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (count : inst.tables.length = start.val)
    (base : Nat) (initial : List Nat) (allocationStart : Nat) (original : List tableinst)
    (startOrder : allocationStart ≤ start.val)
    (ordered : AddressOrder base initial store.tables.length (inst.tables.val.map fun address => address.index.val))
    (matching : AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
      seed.module.module.env.table_types.val allocationStart original (store.tables.val.map decodeTable) start.val) :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        AddressOrder base initial after.tables.length (next.tables.val.map fun address => address.index.val) ∧
        (status = .Ok () → AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
          seed.module.module.env.table_types.val allocationStart original (after.tables.val.map decodeTable)
          seed.module.module.env.table_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      allocationStart ≤ state.2.2.1.val ∧
      AddressOrder base initial state.1.tables.length (state.2.2.2.tables.val.map fun address => address.index.val) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
        seed.module.module.env.table_types.val allocationStart original (state.1.tables.val.map decodeTable) state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexLower, currentOrder, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexLower currentOrder indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, currentOrder, by simp⟩
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
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, effect.address_order currentOrder, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have grown := (typed rfl).append indexLower within
          have actual := effect.decoded success
          dsimp only at actual
          unfold AllocationPrefix
          rw [actual]
          simpa only [AllocationPrefix, source, increment] using grown
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, currentOrder, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startOrder, ordered, startBound, (fun _ => count), (fun _ => matching)⟩


/-- An accepted full table allocation run has the exact source-defined append
and the consecutive address map required by module allocation. -/
theorem table_allocation_success {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before after : runtime.store.Store M) (inst next : runtime.store.ModuleInst) (start : Usize)
    (bound : start.val ≤ inst.module.module.env.table_types.val.length)
    (objectBound : objectCount before ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < before.tables.length)
    (count : inst.tables.length = start.val)
    (run : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator before (.Ok ()) start inst =
      .ok (typeParts after (.Ok ()) next)) :
    after.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      (inst.module.module.env.table_types.val.drop start.val).map
        (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty)) ∧
    after.tables.length = before.tables.length + (inst.module.module.env.table_types.val.length - start.val) ∧
    next.tables.val.map (fun address => address.index.val) =
      inst.tables.val.map (fun address => address.index.val) ++
        List.range' before.tables.length (inst.module.module.env.table_types.val.length - start.val) := by
  have checked := table_allocation_staging_loop memory allocator law before before inst inst start bound rfl rfl
    (.refl _) objectBound issued count before.tables.length (inst.tables.val.map fun address => address.index.val)
    start.val (before.tables.val.map decodeTable) (by omega) (.refl _ _) (.initial _ _ _ _)
  rw [run, WP.spec_ok] at checked
  obtain ⟨actual, actualInst, status, same, changed, instChanged, retained, objects, addresses, finalCount, ordered, contents⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := (type_parts_inj _ _ _ _ _ _).mp same
  have fullCount := finalCount rfl
  have complete := ordered.complete (count := inst.module.module.env.table_types.val.length - start.val)
    (by simp only [List.length_map]; change next.tables.length = inst.tables.length + _; omega)
  exact ⟨(contents rfl).complete, complete.1, complete.2⟩

end Itasca.Runtime.Store

end

/-! ## TableBindingLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table allocation loop retains import-compatible table types and limits,
while retaining all old store objects and all other provisional maps. -/
theorem table_binding_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (count : inst.tables.length = start.val)
    (matching : TableBindings store (seed.module.module.env.table_types.val.take start.val) inst.tables.val) :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        (status = .Ok () → TableBindings after seed.module.module.env.table_types.val next.tables.val) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → TableBindings state.1 (seed.module.module.env.table_types.val.take state.2.2.1.val) state.2.2.2.tables.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, by simp⟩
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
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTyped := effect.table_bindings (typed rfl) success
          simpa only [source, increment, List.take_succ_eq_append_getElem within] using nextTyped
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd, List.take_length] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => matching)⟩

end Itasca.Runtime.Store

end

/-! ## GlobalStagingCauses -/

section

/-!
Global staging resource causes from definition through initialization and the staging loop. Actual allocation requests and initializer failures remain distinct explanations of errors.
-/

/-! ## Global Allocation Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def GlobalAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.globals 1#usize = .ok (false,store.globals)
  | _ => False

theorem define_global_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value)
    (bound : objectCount store ≤ Usize.max) (typed : ty.valtype = Interp.rawType value)
    (owned : ValueInStore store value) :
    runtime.store.Store.define_global_with memory allocator store ty value
      ⦃ out => ∀ error, out.1 = .Err error → out.2 = store ∧ GlobalAllocationCause allocator store error ⦄ := by
  obtain ⟨words,encoded,_⟩ := WP.spec_imp_exists (Interp.encode_value_spec value store.id owned.1)
  unfold runtime.store.Store.define_global_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    rw [check_value_owned memory store value owned.1]
    simp [typed,core.result.Result.Insts.CoreOpsTry.branch,
      core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default]
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.globals 1#usize
    rw [reserved]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,GlobalAllocationCause,refusal]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,encoded]
      cases words with
      | mk lo hi =>
        simp
        have max : store.globals.length < Usize.max := by unfold objectCount at space; scalar_tac
        step
        simp
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,GlobalAllocationCause]
    omega
end Itasca.Runtime.Store

end

/-! ## Global Initializer Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_global_resource_cause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (bound : objectCount store ≤ Usize.max)
    (error : runtime.ExecError) (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index = .ok (.Err error,after,host)) :
    after = store ∧ host = platform ∧
      (Interp.SyntheticPreparationCause allocator store code error ∨ GlobalAllocationCause allocator store error) := by
  obtain ⟨evaluated, evalRun, sameStore, sameHost, success⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code global.init global.gtype.valtype words hi hc compiled resolved bindings)
  rcases evaluated with ⟨value, after, host⟩
  dsimp only at sameStore sameHost success evalRun
  subst after host
  have errors := eval_const_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved
    (initializer_reference_bound resolved bindings)
  rw [evalRun] at errors
  simp only [WP.spec_ok] at errors
  unfold runtime.store.instantiate.Store.add_instance_global at run
  simp only [Compiler.initializer_vec_index store.instances instIndex inst hi,
    runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg)] at run
  simp only [bind_ok,
    Compiler.initializer_vec_index inst.module.global_initializers index function hmapping,
    evalRun] at run
  cases value with
  | Err rejected =>
    have cause := errors.2.2.2 rejected rfl
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl cause⟩
  | Ok value =>
    obtain ⟨owned,typed⟩ := success value rfl
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨⟨status,changed⟩,defined,run⟩ := normal_bind_exists _ _ _ run
    have cause := define_global_resource_causes memory allocator law store global.gtype value bound typed.symm owned
    rw [defined,WP.spec_ok] at cause
    cases status with
    | Err rejected =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      obtain ⟨same,cause⟩ := cause rejected rfl
      exact ⟨same,rfl,Or.inr cause⟩
    | Ok address =>
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
      obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [uncurry_apply_pair] at run
      obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
      simp at run
end Itasca.Runtime.Store

end

/-! ## Global Staging Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev globalStageCall {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (instIndex : Usize)
    (state : runtime.store.Store M × P) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator state.1 state.2 instIndex index

def GlobalStagingCause {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (platform : P)
    (instIndex start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current host index inst global function code,
    PreparationCalls (globalStageCall memory hooks floats allocator instIndex) (store,platform) start (current,host) index ∧
    current.instances.val[instIndex.val]? = some inst ∧
    inst.module.module.env.globals.val[index.val]? = some global ∧
    inst.module.global_initializers.val[index.val]? = some function ∧
    inst.module.functions.val[function.val]? = some code ∧
    Compiler.InitializerCode code global.init global.gtype.valtype ∧
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator current host instIndex index = .ok (.Err error,current,host) ∧
    (Interp.SyntheticPreparationCause allocator current code error ∨ GlobalAllocationCause allocator current error)

theorem global_staging_resource_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧
        (∀ error, finalStatus = .Err error → GlobalStagingCause memory hooks floats allocator store platform instIndex start error) ∧
        ErrorAllowed ResourceError finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧
      (state.2.2.1 = .Ok () → PreparationCalls (globalStageCall memory hooks floats allocator instIndex) (store,platform) start (state.1,state.2.1) state.2.2.2) ∧
      (∀ error, state.2.2.1 = .Err error → GlobalStagingCause memory hooks floats allocator store platform instIndex start error) ∧ ErrorAllowed ResourceError state.2.2.1 ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, trace, causes, errors, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData⟩
    dsimp only at hhost errors hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env.eq,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        have reached := trace rfl
        obtain ⟨⟨state,after,host'⟩,called,⟨effect,hhost'⟩,nextErrors⟩ := WP.spec_imp_exists (normal_return_post
          (add_instance_global_effect memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room)
          (fun out called => add_global_errors memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings out called))
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        dsimp only at effect hhost' nextErrors
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨?_,?_,nextErrors, nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData⟩, ?_⟩
        · intro success
          subst state
          exact .next reached called hnext
        · intro error rejected
          subst state
          obtain ⟨sameStore,sameHost,cause⟩ := add_global_resource_cause memory hooks floats allocator law
            current platform instIndex index currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings
            hobjects error after platform called
          subst after
          exact ⟨current,platform,index,currentInst,global,function,code,reached,hfound,hglobal,hmapping,hc,hcompiled,called,cause⟩
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
  · exact ⟨rfl, (fun _ => .refl _ _), (by simp), True.intro, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl⟩

end Itasca.Runtime.Store

end

end
