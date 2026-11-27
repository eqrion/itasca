import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Store.Invariant.FunctionAndTypeStagingCauses
import Itasca.Runtime.Integration.Execution.Mutation.Operations

/-!
Proofs for Runtime / Integration / Api.

This module collects StoreDefine, StoreWrite.
Each section documents its contracts and consumers.
-/

/-! ## StoreDefine -/

section

open Itasca.Representation

/-! Public store definitions preserve executable certificates and expose the
exact appended object or unchanged store on failure. -/

namespace Itasca.Integration
open Aeneas Aeneas.Std Store

/-- Appending an external identity changes reference bounds but no decoded
source object or executable function certificate. -/
theorem ExecutableInv.append_extern {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {store : runtime.store.Store M}
    (held : ExecutableInv view code store) (identity : U64) (externs : alloc.vec.Vec U64)
    (appended : externs.val = store.externs.val ++ [identity])
    (room : objectCount store < store.limits.max_objects.val) :
    ExecutableInv view code {store with externs} := by
  have length : externs.length = store.externs.length + 1 := by
    simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
  have growth : store.externs.length ≤ externs.length := by omega
  have shape : Shape view {store with externs} := by
    refine ⟨held.shape.identity, held.shape.functions, held.shape.memories, ?_, ?_, ?_,
      held.shape.instances, held.shape.canonicalTypes, ?_, held.shape.instanceLimit,
      held.shape.instanceAccounting, held.shape.instanceItemLimit, held.shape.signatureAccounting,
      held.shape.signatureLimit, held.shape.memoryAccounting, held.shape.memoryLimit,
      held.shape.tableAccounting, held.shape.tableLimit⟩
    · intro table member
      exact TableShape.mono store {store with externs} (Nat.le_refl _) growth table
        (held.shape.tables table member)
    · intro global member
      exact GlobalShape.mono store {store with externs} (Nat.le_refl _) growth global
        (held.shape.globals global member)
    · intro element member word present
      exact ReferenceShape.mono store {store with externs} (Nat.le_refl _) growth _ _
        (held.shape.elements element member word present)
    · dsimp only
      unfold objectCount at room
      omega
  exact {
    shape := shape, storeSyntax := held.storeSyntax, typed := held.typed,
    supported := held.supported, compiled := held.compiled,
    segmentBounds := ⟨held.segmentBounds.elements, held.segmentBounds.data⟩,
    exportBounds := held.exportBounds,
    segmentAccounting := ⟨held.segmentAccounting.elements, held.segmentAccounting.datas⟩,
    capacities := held.capacities }

/-- Defining an external identity preserves executable metadata and the decoded
source store. Failure leaves the store unchanged; success appends one owned identity. -/
@[step] theorem _root_.Itasca.runtime.store.Store.define_extern_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (identity : U64) :
    runtime.store.Store.define_extern_with memory allocator store identity ⦃ (result, after) =>
      ExecutableInv view code after ∧ Store.MetadataPreserved store after ∧
      after.limits = store.limits ∧ decodeStore view code after = decodeStore view code store ∧
      match result with
      | .Err _ => after = store
      | .Ok address =>
        address.store = store.id ∧ address.index.val = store.externs.length ∧
        ValueInStore after (.ExternRef (some address)) ∧
        ∃ externs : alloc.vec.Vec U64, externs.val = store.externs.val ++ [identity] ∧
          after = {store with externs} ⦄ := by
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  unfold runtime.store.Store.define_extern_with
  step with room_spec memory store bound as ⟨room, roomEq⟩
  rw [roomEq]
  by_cases space : objectCount store < store.limits.max_objects.val
  · simp only [if_pos space, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserve⟩ := reserve_wrapper_eq allocator law store.externs 1#usize
    rw [reserve]
    cases answer
    · simp only [Bool.false_eq_true, if_false, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, Store.MetadataPreserved.refl store, trivial, trivial, trivial⟩
    · simp only [ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have available : store.externs.length < Usize.max := by
        unfold objectCount at space
        scalar_tac
      step as ⟨externs, appended⟩
      refine ⟨held.append_extern identity externs appended space, ⟨rfl, rfl, rfl, rfl⟩,
        rfl, rfl, ?_, externs, appended, rfl⟩
      · simp only [ValueInStore, Representation.ValueOwnedFits, alloc.vec.Vec.len_val,
          alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
        refine ⟨⟨trivial, available, ?_⟩, by omega⟩
        have widths := Usize.bounds_eq
        rcases widths with narrow | wide
        · rw [narrow] at available
          exact Nat.lt_trans available (by scalar_tac)
        · rwa [wide] at available
  · simp only [if_neg space, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, Store.MetadataPreserved.refl store, trivial, trivial, trivial⟩

/-- A successful canonical signature lookup and host append preserve all
executable certificates, provided the final function fits the object budget. -/
theorem ExecutableInv.append_host {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {store interned : runtime.store.Store M}
    (held : ExecutableInv view code store) (ty : Itasca.wasm_types.FuncType)
    (signature : Usize) (host : U64)
    (effect : InternEffect store ty (.Ok signature, interned))
    (room : objectCount interned < interned.limits.max_objects.val)
    (functions : alloc.vec.Vec runtime.store.FuncInst)
    (appended : functions.val = interned.funcs.val ++ [{signature, code := .Host host}]) :
    ExecutableInv view code {interned with funcs := functions} ∧
      StagedPrefix store {interned with funcs := functions} ∧
      Extend_store (decodeStore view code store)
        (decodeStore view code {interned with funcs := functions}) := by
  have retained := effect.staged
  have onlyTypes := effect.only_types
  have funcsEq : interned.funcs = store.funcs := congrArg (fun s => s.funcs) onlyTypes
  have instances : interned.instances = store.instances := congrArg (fun s => s.instances) onlyTypes
  have elements : interned.elems = store.elems := congrArg (fun s => s.elems) onlyTypes
  have datas : interned.datas = store.datas := congrArg (fun s => s.datas) onlyTypes
  have pushed : StagedPrefix interned {interned with funcs := functions} := by
    constructor <;> simp only [appended, alloc.vec.Vec.length, List.take_left, List.take_length]
  have combined := retained.trans pushed
  have allocated := effect.allocated held.shape.allocated
  have grown : interned.funcs.length ≤ functions.length := by
    simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
    omega
  have allocation : AllocationShape view {interned with funcs := functions} := by
    refine ⟨allocated.identity, allocated.memories, ?_, ?_, ?_, allocated.canonicalTypes,
      ?_, allocated.signatureAccounting, allocated.signatureLimit, allocated.memoryAccounting,
      allocated.memoryLimit, allocated.tableAccounting, allocated.tableLimit⟩
    · intro table member
      exact TableShape.mono interned {interned with funcs := functions} grown (Nat.le_refl _) table (allocated.tables table member)
    · intro global member
      exact GlobalShape.mono interned {interned with funcs := functions} grown (Nat.le_refl _) global (allocated.globals global member)
    · intro element member word present
      exact ReferenceShape.mono interned {interned with funcs := functions} grown (Nat.le_refl _) _ _
        (allocated.elements element member word present)
    · simp only [objectCount, alloc.vec.Vec.length, appended,
        List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
  have shaped : Shape view {interned with funcs := functions} := by
    apply held.shape.of_allocated allocation combined instances
    intro function member
    change function ∈ functions.val at member
    rw [appended, funcsEq] at member
    rcases List.mem_append.mp member with old | fresh
    · exact combined.function_shape function (held.shape.functions function old)
    · have same := List.mem_singleton.mp fresh
      subst function
      exact ⟨(List.getElem?_eq_some_iff.mp effect.lookup).1, trivial⟩
  have fresh : ∀ function ∈ functions.val,
      function ∈ store.funcs.val ∨ ∃ id, function.code = .Host id := by
    intro function member
    rw [appended, funcsEq] at member
    rcases List.mem_append.mp member with old | added
    · exact Or.inl old
    · have same := List.mem_singleton.mp added
      subst function
      exact Or.inr ⟨host, rfl⟩
  obtain ⟨valid, extended⟩ := held.append_hosts combined shaped instances elements datas fresh
  exact ⟨valid, combined, extended⟩

/-- The two-object reservation leaves room for the host after a fresh
signature; reusing a signature consumes only the host's slot. -/
private theorem host_intern_room {M : Type} {store interned : runtime.store.Store M}
    (ty : Itasca.wasm_types.FuncType) (index signature : Usize)
    (found : store.types.val[index.val]? = some ty ∨ index.val = store.types.length)
    (space : objectCount store < store.limits.max_objects.val)
    (booked : objectCount store + (if index = store.types.len then 2#usize else 1#usize).val ≤
      store.limits.max_objects.val)
    (effect : InternEffect store ty (.Ok signature, interned)) :
    objectCount interned < interned.limits.max_objects.val := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, lookup, existing⟩ |
    ⟨types, count, appended, fresh, capacity, counted, limited, created⟩
  · cases failed
  · cases existing
    exact space
  · have atEnd : index = store.types.len := by
      rcases found with lookup | atEnd
      · exact False.elim (fresh (List.mem_of_getElem? lookup))
      · apply UScalar.eq_of_val_eq
        exact atEnd
    simp only [atEnd, ite_true, UScalar.ofNatCore_val_eq] at booked
    cases created
    simp only [objectCount, alloc.vec.Vec.length, appended,
      List.length_append, List.length_singleton]
    unfold objectCount at booked
    simp only [alloc.vec.Vec.length] at booked
    omega

/-- A host definition either leaves the store unchanged or appends an issued
host with its exact structural signature, preserving executable certificates. -/
@[step] theorem _root_.Itasca.runtime.store.Store.define_host_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.FuncType) (host : U64) :
    runtime.store.Store.define_host_with memory allocator store ty host ⦃ (result, after) =>
      ExecutableInv view code after ∧ StagedPrefix store after ∧
      Extend_store (decodeStore view code store) (decodeStore view code after) ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.funcs.length ∧
        ExternalIssued after (.Func address) ∧ ValueInStore after (.FuncRef (some address)) ∧
        WebAssembly.HostFunction (decodeStore view code after) address.index.val host.val
          (ty.params.val.map Itasca.Translation.valueType) (ty.results.val.map Itasca.Translation.valueType) ⦄ := by
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  unfold runtime.store.Store.define_host_with
  step with runtime.store.Store.find_type.spec memory store ty as ⟨index, valid, prior, found⟩
  have selected : (if index = store.types.len then Result.ok 2#usize else Result.ok 1#usize) =
      Result.ok (if index = store.types.len then 2#usize else 1#usize) := by
    split <;> rfl
  rw [selected]
  simp only [bind_ok]
  step with runtime.store.Store.room_for.spec memory store
    (if index = store.types.len then 2#usize else 1#usize) bound as ⟨room, roomEq⟩
  rw [roomEq]
  by_cases booked : objectCount store < store.limits.max_objects.val ∧
      objectCount store + (if index = store.types.len then 2#usize else 1#usize).val ≤
        store.limits.max_objects.val
  · simp only [if_pos booked, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserve⟩ := reserve_wrapper_eq allocator law store.funcs 1#usize
    rw [reserve]
    cases answer
    · simp only [Bool.false_eq_true, if_false, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, .refl _, Spec.extend_store_refl _ held.well_formed, trivial⟩
    · simp only [ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with intern_type_effect memory allocator law store ty bound as ⟨status, interned, effect⟩
      cases status with
      | Err error =>
        have unchanged : interned = store := by
          rcases effect with ⟨cause, failed⟩ | ⟨canonical, lookup, existing⟩ |
            ⟨types, count, appended, fresh, capacity, counted, limited, created⟩
          · exact (Prod.mk.inj failed).2
          · cases existing
          · cases created
        subst interned
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
        exact ⟨held, .refl _, Spec.extend_store_refl _ held.well_formed, trivial⟩
      | Ok signature =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have space := host_intern_room ty index signature found booked.1 booked.2 effect
        have available : interned.funcs.length < Usize.max := by
          unfold objectCount at space
          scalar_tac
        step as ⟨functions, appended⟩
        obtain ⟨certified, retained, extension⟩ :=
          held.append_host ty signature host effect space functions appended
        have funcsEq : interned.funcs = store.funcs := congrArg (fun s => s.funcs) effect.only_types
        have identity : interned.id = store.id := effect.staged.identity
        have length : functions.length = interned.funcs.length + 1 := by
          simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
        have fits64 : interned.funcs.length < U64.max := by
          rcases Usize.bounds_eq with narrow | wide
          · rw [narrow] at available
            exact Nat.lt_trans available (by scalar_tac)
          · rwa [wide] at available
        refine ⟨certified, retained, extension, identity, ?_, ?_, ?_, ?_⟩
        · simp only [alloc.vec.Vec.len_val, funcsEq]
        · intro owned
          change interned.funcs.len.val < functions.length
          rw [alloc.vec.Vec.len_val, length]
          omega
        · exact ⟨⟨rfl, available, fits64⟩, by change interned.funcs.len.val < functions.length; rw [alloc.vec.Vec.len_val, length]; omega⟩
        · apply decode_host_function view code {interned with funcs := functions}
            ⟨interned.id, interned.funcs.len⟩ {signature, code := .Host host} host ty
          · simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, appended,
              List.getElem?_append, lt_self_iff_false, if_false, Nat.sub_self, List.getElem?_cons_zero]
          · rfl
          · exact effect.lookup
  · simp only [if_neg booked, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, .refl _, Spec.extend_store_refl _ held.well_formed, trivial⟩

/-- Defining memory retains the supplied buffer bytes, establishes the declared
page bounds, and preserves the executable store. Every failure is atomic. -/
@[step] theorem _root_.Itasca.runtime.store.Store.define_memory_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.MemType) (buffer : M) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.memories.length ∧
        ExternalIssued after (.Memory address) ∧
        after.memories.val = store.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧
        (view buffer).length = ty.limits.min.val * 65536 ⦄ := by
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  step with define_memory_effect memory allocator law view laws store ty buffer bound
    as ⟨result, after, effect⟩
  rcases effect with ⟨error, failed⟩ |
    ⟨memories, count, appended, fit, size, room, counted, limited, created⟩
  · rcases failed with ⟨rfl, rfl⟩
    exact ⟨held, ⟨.refl _, rfl, held.shape, held.segmentBounds,
      Spec.extend_store_refl _ held.well_formed, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · rcases created with ⟨rfl, rfl⟩
    have canonical : MemoryShape view {buf := buffer, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [size, Nat.mul_mod_left]
      · simpa only [size, Nat.mul_div_left _ (n := 65536) (by decide), UScalar.ofNatCore_val_eq] using fit.1
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have bounds := fit.2
        rw [maximumEq] at bounds
        simpa only [size, Nat.mul_div_left _ (n := 65536) (by decide), UScalar.ofNatCore_val_eq] using bounds
    have old := held.shape.allocated
    have allocated : AllocationShape view {store with memories, memory_bytes := count} := by
      refine ⟨old.identity, ?_, old.tables, old.globals, old.elements, old.canonicalTypes,
        ?_, old.signatureAccounting, old.signatureLimit, ?_, limited,
        old.tableAccounting, old.tableLimit⟩
      · intro item member
        change item ∈ memories.val at member
        rw [appended] at member
        rcases List.mem_append.mp member with prior | added
        · exact old.memories item prior
        · have same := List.mem_singleton.mp added
          subst item
          exact canonical
      · simp only [objectCount, alloc.vec.Vec.length, appended,
          List.length_append, List.length_singleton]
        unfold objectCount at room
        simp only [alloc.vec.Vec.length] at room
        omega
      · change count.val = (memories.val.map fun item => (view item.buf).length).sum
        simp only [appended, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [counted, old.memoryAccounting]
    have retained : StagedPrefix store {store with memories, memory_bytes := count} := by
      constructor <;> simp only [appended, alloc.vec.Vec.length, List.take_left, List.take_length]
    have shaped : Shape view {store with memories, memory_bytes := count} :=
      held.shape.of_allocated allocated retained rfl
        (fun function member => retained.function_shape function (held.shape.functions function member))
    obtain ⟨certified, extension⟩ := held.append_hosts retained shaped rfl rfl rfl
      (fun _ member => Or.inl member)
    refine ⟨certified, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, shaped,
      ⟨held.segmentBounds.elements, held.segmentBounds.data⟩, extension, ⟨rfl, rfl⟩, rfl⟩,
      rfl, rfl, ?_, appended, size⟩
    intro owned
    change store.memories.len.val < memories.length
    simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, appended,
      List.length_append, List.length_singleton]
    omega

/-- Defining a table appends exactly the declared number of null references;
all rejection and allocation failures leave the original store unchanged. -/
@[step] theorem _root_.Itasca.runtime.store.Store.define_table_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.TableType) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.tables.length ∧
        ExternalIssued after (.Table address) ∧
        ∃ elements : alloc.vec.Vec U64, elements.val = List.replicate ty.limits.min.val 0#u64 ∧
          after.tables.val = store.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ⦄ := by
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  step with define_table_effect memory allocator law store ty bound as ⟨result, after, effect⟩
  rcases effect with ⟨error, failed⟩ |
    ⟨tables, elements, count, zeros, appended, fit, room, counted, limited, created⟩
  · rcases failed with ⟨rfl, rfl⟩
    exact ⟨held, ⟨.refl _, rfl, held.shape, held.segmentBounds,
      Spec.extend_store_refl _ held.well_formed, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · rcases created with ⟨rfl, rfl⟩
    have canonical : TableShape store {elements, ty := ty.elem, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [alloc.vec.Vec.length, zeros, List.length_replicate]
        scalar_tac
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have limits := fit.2
        rw [maximumEq] at limits
        simpa only [alloc.vec.Vec.length, zeros, List.length_replicate] using limits.1
      · intro word member
        rw [zeros] at member
        have zero := (List.mem_replicate.mp member).2
        subst word
        exact Or.inl rfl
    have old := held.shape.allocated
    have allocated : AllocationShape view {store with tables, table_elements := count} := by
      refine ⟨old.identity, old.memories, ?_, old.globals, old.elements, old.canonicalTypes,
        ?_, old.signatureAccounting, old.signatureLimit, old.memoryAccounting, old.memoryLimit,
        ?_, limited⟩
      · intro item member
        change item ∈ tables.val at member
        rw [appended] at member
        rcases List.mem_append.mp member with prior | added
        · exact old.tables item prior
        · have same := List.mem_singleton.mp added
          subst item
          exact canonical
      · simp only [objectCount, alloc.vec.Vec.length, appended,
          List.length_append, List.length_singleton]
        unfold objectCount at room
        simp only [alloc.vec.Vec.length] at room
        omega
      · change count.val = (tables.val.map fun item => item.elements.length).sum
        simp only [appended, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
          alloc.vec.Vec.length, zeros, List.length_replicate]
        rw [counted, old.tableAccounting]
    have retained : StagedPrefix store {store with tables, table_elements := count} := by
      constructor <;> simp only [appended, alloc.vec.Vec.length, List.take_left, List.take_length]
    have shaped : Shape view {store with tables, table_elements := count} :=
      held.shape.of_allocated allocated retained rfl
        (fun function member => retained.function_shape function (held.shape.functions function member))
    obtain ⟨certified, extension⟩ := held.append_hosts retained shaped rfl rfl rfl
      (fun _ member => Or.inl member)
    refine ⟨certified, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, shaped,
      ⟨held.segmentBounds.elements, held.segmentBounds.data⟩, extension, ⟨rfl, rfl⟩, rfl⟩,
      rfl, rfl, ?_, elements, zeros, appended⟩
    intro owned
    change store.tables.len.val < tables.length
    simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, appended,
      List.length_append, List.length_singleton]
    omega

/-- A global definition accepts only an owned value of its declared type.
Success appends the exact decoded value; every rejection preserves the store. -/
@[step] theorem _root_.Itasca.runtime.store.Store.define_global_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value) (issued : IssuedValue store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.globals.length ∧
        ExternalIssued after (.Global address) ∧ ty.valtype = Representation.rawType value ∧
        (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS ++
          [⟨.mk_globaltype (Itasca.Translation.mutability ty.mutability) (Itasca.Translation.valueType ty.valtype),
            Representation.sourceValue value⟩] ⦄ := by
  classical
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  by_cases accepted : Interp.OwnedBy store.id value ∧ ty.valtype = Representation.rawType value
  · have owned := issued.in_store accepted.1
    step with define_global_effect memory allocator law store ty value bound accepted.2 owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, appended, room, created⟩
    · rcases failed with ⟨rfl, rfl⟩
      exact ⟨held, ⟨.refl _, rfl, held.shape, held.segmentBounds,
        Spec.extend_store_refl _ held.well_formed, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
    · rcases created with ⟨rfl, rfl⟩
      have canonical := encode_global_shape store value ty accepted.2 owned
      rw [encoded] at canonical
      simp only [WP.spec_ok] at canonical
      have old := held.shape.allocated
      have allocated : AllocationShape view {store with globals} := by
        refine ⟨old.identity, old.memories, old.tables, ?_, old.elements, old.canonicalTypes,
          ?_, old.signatureAccounting, old.signatureLimit, old.memoryAccounting, old.memoryLimit,
          old.tableAccounting, old.tableLimit⟩
        · intro item member
          change item ∈ globals.val at member
          rw [appended] at member
          rcases List.mem_append.mp member with prior | added
          · exact old.globals item prior
          · have same := List.mem_singleton.mp added
            subst item
            exact canonical
        · simp only [objectCount, alloc.vec.Vec.length, appended,
            List.length_append, List.length_singleton]
          unfold objectCount at room
          simp only [alloc.vec.Vec.length] at room
          omega
      have retained : StagedPrefix store {store with globals} := by
        constructor <;> simp only [appended, alloc.vec.Vec.length, List.take_left, List.take_length]
      have shaped : Shape view {store with globals} :=
        held.shape.of_allocated allocated retained rfl
          (fun function member => retained.function_shape function (held.shape.functions function member))
      obtain ⟨certified, extension⟩ := held.append_hosts retained shaped rfl rfl rfl
        (fun _ member => Or.inl member)
      refine ⟨certified, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, shaped,
        ⟨held.segmentBounds.elements, held.segmentBounds.data⟩, extension, ⟨rfl, rfl⟩, rfl⟩,
        rfl, rfl, ?_, accepted.2, ?_⟩
      · intro sameStore
        change store.globals.len.val < globals.length
        simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, appended,
          List.length_append, List.length_singleton]
        omega
      · change globals.val.map decodeGlobal = store.globals.val.map decodeGlobal ++ _
        rw [appended, List.map_append]
        simp only [List.map_cons, List.map_nil, decodeGlobal]
        rw [accepted.2, decode_encoded_value store value owned words encoded]
  · have rejected : (∃ error, runtime.store.Store.check_value memory store value = .ok (.Err error)) ∨
        (runtime.store.Store.check_value memory store value = .ok (.Ok ()) ∧
          core.cmp.PartialEq.ne.trait_default Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType
            ty.valtype (Representation.rawType value) = .ok true) := by
      obtain ⟨checked, run, same⟩ := WP.spec_imp_exists (Interp.check_value_eq memory store value)
      subst checked
      by_cases owner : Interp.OwnedBy store.id value
      · right
        refine ⟨?_, ?_⟩
        · simpa only [Interp.checkOwner, if_pos owner] using run
        · have mismatch : ty.valtype ≠ Representation.rawType value := fun same => accepted ⟨owner, same⟩
          rw [Interp.value_type_ne_eq, if_neg mismatch]
      · left
        exact ⟨.WrongStore, by simpa only [Interp.checkOwner, if_neg owner] using run⟩
    step with define_global_rejected memory allocator store ty value bound rejected
      as ⟨result, after, error, failed, unchanged⟩
    subst result after
    exact ⟨held, ⟨.refl _, rfl, held.shape, held.segmentBounds,
      Spec.extend_store_refl _ held.well_formed, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Sufficient object/signature budgets and granted allocations make host
definition succeed. The two object slots cover a new signature and the host. -/
theorem define_host_available {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (grants : Platform.AllocationAvailable allocator (2 * Usize.max))
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType) (host : U64)
    (objects : objectCount store + 2 ≤ store.limits.max_objects.val)
    (signatureSize : ty.params.length + ty.results.length ≤ Usize.max)
    (signatures : store.signature_values.val + ty.params.length + ty.results.length ≤
      store.limits.max_signature_values.val) :
    runtime.store.Store.define_host_with memory allocator store ty host ⦃ (result, _) =>
      ∃ address, result = .Ok address ⦄ := by
  have bound : objectCount store ≤ Usize.max := by scalar_tac
  have typesGranted := grants _ store.types 1#usize (by scalar_tac)
  have paramsGranted := grants _ (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.params.len (by scalar_tac)
  have resultsGranted := grants _ (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.results.len (by scalar_tac)
  have noCopyRefusal : ¬TypeCopyRefusal allocator ty := by
    simp only [TypeCopyRefusal, paramsGranted, resultsGranted, Result.ok.injEq,
      Prod.mk.injEq, Bool.true_eq_false, false_and, or_self, not_false_eq_true]
  obtain ⟨internResult, internRun, internEffect⟩ := WP.spec_imp_exists
    (intern_type_effect memory allocator law store ty bound)
  have resourceErrors := intern_type_resource_causes memory allocator law store ty bound
  rw [internRun] at resourceErrors
  simp only [WP.spec_ok] at resourceErrors
  have internSuccess : ∃ signature, internResult.1 = .Ok signature := by
    cases status : internResult.1 with
    | Ok signature => exact ⟨signature, rfl⟩
    | Err error =>
      have cause := (resourceErrors error status).2.2
      cases error <;> simp only [TypeInternResourceCause] at cause
      case Exhausted resource =>
        cases resource <;> simp only [TypeInternResourceCause] at cause
        case Allocation =>
          rcases cause with refused | refused
          · rw [typesGranted] at refused
            simp only [Result.ok.injEq, Prod.mk.injEq, Bool.true_eq_false, false_and] at refused
          · exact False.elim (noCopyRefusal refused)
        case Objects => omega
  obtain ⟨signature, internSuccess⟩ := internSuccess
  unfold runtime.store.Store.define_host_with
  step with runtime.store.Store.find_type.spec memory store ty as ⟨index, valid, prior, found⟩
  have selected : (if index = store.types.len then Result.ok 2#usize else Result.ok 1#usize) =
      Result.ok (if index = store.types.len then 2#usize else 1#usize) := by
    split <;> rfl
  rw [selected]
  simp only [bind_ok]
  step with runtime.store.Store.room_for.spec memory store
    (if index = store.types.len then 2#usize else 1#usize) bound as ⟨room, roomEq⟩
  have booked : objectCount store < store.limits.max_objects.val ∧
      objectCount store + (if index = store.types.len then 2#usize else 1#usize).val ≤ store.limits.max_objects.val := by
    split <;> scalar_tac
  rw [roomEq]
  simp only [if_pos booked, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨answer, reserve, reserveCall⟩ := reserve_with_cause allocator law store.funcs 1#usize
  have funcsGranted := grants _ store.funcs 1#usize (by scalar_tac)
  rw [funcsGranted] at reserveCall
  have accepted : answer = true := by
    simpa only [Result.ok.injEq, Prod.mk.injEq, and_true, eq_comm] using reserveCall
  subst answer
  simp only [ite_true] at reserve
  simp only [reserve, internRun, bind_ok, internSuccess, core.result.Result.Insts.CoreOpsTry.branch]
  have effect : InternEffect store ty (.Ok signature, internResult.2) := by
    simpa only [←internSuccess] using internEffect
  have space := host_intern_room ty index signature found booked.1 booked.2 effect
  have room : internResult.2.funcs.length < Usize.max := by
    unfold objectCount at space
    scalar_tac
  step with WP.exists_imp_spec ⟨internResult, internRun, rfl⟩ as ⟨status, interned, same⟩
  subst internResult
  simp only [Prod.fst] at internSuccess
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨functions, appended⟩
  exact ⟨_, rfl⟩

end Itasca.Integration

end

/-! ## StoreWrite -/

section

open Itasca.Representation

/-! Public store writes preserve executable certificates and identify the
requested object that changes. Memory borrows specify their write-back closures. -/

namespace Itasca.Integration
open Aeneas Aeneas.Std Store Interp

/-- Scalar globals have a zero unused high word. -/
private theorem global_high_zero {M : Type} (store : runtime.store.Store M)
    (global : runtime.store.GlobalInst) (shape : GlobalShape store global)
    (scalar : global.ty.valtype ≠ .V128) : global.hi = 0#u64 := by
  cases kind : global.ty.valtype <;> simp only [GlobalShape, kind] at shape
  all_goals first | exact shape | exact shape.2 | exact False.elim (scalar kind)

/-- Setting an issued mutable global writes the requested address and exact
source value. Foreign, immutable, and mistyped writes leave the store unchanged. -/
@[step] theorem _root_.Itasca.runtime.store.Store.set_global.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.GlobalAddr) (value : runtime.Value)
    (issued : ExternalIssued store (.Global address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_global memory store address value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => GlobalMutation store after (sourceValue value) ∧
        ∃ old : runtime.store.GlobalInst, store.globals.val[address.index.val]? = some old ∧
          old.ty.mutability = .Var ∧ old.ty.valtype = rawType value ∧
          (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS.set address.index.val
            ⟨.mk_globaltype (Itasca.Translation.mutability old.ty.mutability) (Itasca.Translation.valueType old.ty.valtype), sourceValue value⟩ ⦄ := by
  classical
  have unchanged := CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds
  unfold runtime.store.Store.set_global
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with check_value_eq memory store value as ⟨checkedValue, valueEq⟩
    rw [valueEq]
    by_cases owner : OwnedBy store.id value
    · simp only [checkOwner, if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have owned := valueIssued.in_store owner
      have position := issued sameStore
      let old := store.globals.val[address.index.val]
      have found : store.globals.val[address.index.val]? = some old := List.getElem?_eq_getElem position
      have restored : store.globals.set address.index old = store.globals := vec_set_current _ _ position
      have indexed := vec_index_mut_eq store.globals address.index old found
      rw [alloc.vec.Vec.index_mut_slice_index] at indexed
      rw [indexed]
      simp only [bind_ok, bind_tc_ok]
      step with mut_ne old.ty.mutability .Var as ⟨different, differentEq⟩
      cases different with
      | true =>
        simp only [ite_true, restored, WP.spec_ok, uncurry_apply_pair]
        exact ⟨held, unchanged, trivial⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have mutable : old.ty.mutability = .Var := by
          by_contra notMutable
          exact Bool.noConfusion (differentEq.mpr notMutable)
        step with value_type_eq value as ⟨kind, kindEq⟩
        subst kind
        rw [value_type_ne_eq]
        simp only [bind_ok, bind_tc_ok]
        by_cases typed : old.ty.valtype = rawType value
        · simp only [if_pos typed, Bool.false_eq_true, if_false]
          obtain ⟨words, encoded, represented⟩ := WP.spec_imp_exists (encode_value_spec value store.id owned.1)
          have canonical := encode_global_shape store value old.ty typed owned
          rw [encoded] at canonical
          simp only [WP.spec_ok] at canonical
          rw [encoded]
          simp only [bind_ok, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
          have high : old.ty.valtype ≠ .V128 → words.2 = old.hi := by
            intro scalar
            exact (global_high_zero store {old with lo := words.1, hi := words.2} canonical scalar).trans
              (global_high_zero store old (held.shape.globals old (List.mem_of_getElem? found)) scalar).symm
          have mutation : GlobalMutation store
              {store with globals := store.globals.set address.index {old with lo := words.1, hi := words.2}}
              (sourceValue value) := by
            refine ⟨address.index, old, words.1, words.2, found, mutable, ?_, ?_, high, rfl⟩
            · rw [source_value_type, typed]
            · rwa [typed]
          have cumulative := global_mutation_cumulative_of_shape view code store _ held.shape
            held.storeSyntax held.segmentBounds _ mutation (source_value_wf value) (source_value_owned store value owned)
          refine ⟨held.update cumulative, cumulative, mutation, old, found, mutable, typed, ?_⟩
          simp only [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeGlobal]
          rw [typed, decode_encoded_value store value owned words encoded]
        · simp only [if_neg typed, ite_true, restored, WP.spec_ok, uncurry_apply_pair]
          exact ⟨held, unchanged, trivial⟩
    · simp only [checkOwner, if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, unchanged, trivial⟩
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, unchanged, trivial⟩

/-- Setting a table updates exactly the issued table and requested element.
All ownership, type, and bounds rejections leave the store unchanged. -/
@[step] theorem _root_.Itasca.runtime.store.Store.set_table.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_table memory store address index value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => ∃ old : runtime.store.TableInst, ∃ words : U64 × U64,
        store.tables.val[address.index.val]? = some old ∧ index.val < old.elements.length ∧
        elementValueType old.ty = rawType value ∧ runtime.value.encode value = .ok words ∧
        ValueInStore store value ∧ TableMutation store after address old words.1 ∧
        after = {store with
          tables := store.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}} ⦄ := by
  classical
  have unchanged := CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds
  unfold runtime.store.Store.set_table
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with check_value_eq memory store value as ⟨checkedValue, valueEq⟩
    rw [valueEq]
    by_cases owner : OwnedBy store.id value
    · simp only [checkOwner, if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have owned := valueIssued.in_store owner
      have position := issued sameStore
      let old := store.tables.val[address.index.val]
      have found : store.tables.val[address.index.val]? = some old := List.getElem?_eq_getElem position
      have restored : store.tables.set address.index old = store.tables := vec_set_current _ _ position
      have indexed := vec_index_mut_eq store.tables address.index old found
      rw [alloc.vec.Vec.index_mut_slice_index] at indexed
      rw [indexed]
      simp only [bind_ok, bind_tc_ok, element_value_type_exact]
      step with value_type_eq value as ⟨kind, kindEq⟩
      subst kind
      rw [value_type_ne_eq]
      simp only [bind_ok, bind_tc_ok]
      by_cases typed : elementValueType old.ty = rawType value
      · simp only [if_pos typed, Bool.false_eq_true, if_false, lift, bind_ok, bind_tc_ok]
        by_cases outside : UScalar.cast .Usize index ≥ old.elements.len
        · simp only [if_pos outside, restored, WP.spec_ok, uncurry_apply_pair]
          exact ⟨held, unchanged, trivial⟩
        · simp only [if_neg outside]
          have inside : index.val < old.elements.length := by
            have castEq := U32.cast_Usize_val_eq index
            scalar_tac
          have actual : (UScalar.cast .Usize index).val < old.elements.length := by
            simpa only [U32.cast_Usize_val_eq] using inside
          let previous := old.elements.val[(UScalar.cast .Usize index).val]
          have lookup : old.elements.val[(UScalar.cast .Usize index).val]? = some previous :=
            List.getElem?_eq_getElem actual
          obtain ⟨words, encoded, represented⟩ := WP.spec_imp_exists (encode_value_spec value store.id owned.1)
          have reference := encode_reference_shape store value old.ty typed owned
          rw [encoded] at reference
          simp only [WP.spec_ok] at reference
          rw [encoded]
          simp only [bind_ok, bind_tc_ok, lift, alloc.vec.Vec.index_mut_slice_index]
          have element := vec_index_mut_eq old.elements (UScalar.cast .Usize index) previous lookup
          rw [alloc.vec.Vec.index_mut_slice_index] at element
          rw [element]
          simp only [bind_ok, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
          have mutation : TableMutation store
              {store with
                tables := store.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}}
              address old words.1 := by
            refine ⟨_, rfl, ?_, ?_⟩
            · simp only [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq, List.length_set]
            · intro word member
              exact List.mem_or_eq_of_mem_set (by simpa only [alloc.vec.Vec.set_val_eq] using member)
          have cumulative := table_mutation_cumulative_of_shape view code store _ held.shape
            held.storeSyntax held.segmentBounds address old words.1 found mutation reference
          exact ⟨held.update cumulative, cumulative, old, words, found, inside, typed, rfl, owned, mutation, rfl⟩
      · simp only [if_neg typed, ite_true, restored, WP.spec_ok, uncurry_apply_pair]
        exact ⟨held, unchanged, trivial⟩
    · simp only [checkOwner, if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, unchanged, trivial⟩
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, unchanged, trivial⟩

/-- A mutable memory borrow preserves executable certificates when the caller
writes back the same number of bytes. An error reply restores the original
visible bytes through the platform closure, without equating opaque buffers. -/
@[step] theorem _root_.Itasca.runtime.store.Store.memory_mut.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.MemoryAddr) (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory_mut memory store address ⦃ (result, back) =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id ∧
        ∀ reply, ExecutableInv view code (back reply) ∧
          CumulativeStoreMutation view code store (back reply) ∧ back reply = store
      | .Ok bytes => ∃ object : runtime.store.MemInst M,
        address.store = store.id ∧ store.memories.val[address.index.val]? = some object ∧
        bytes = view object.buf ∧
        (∀ replacement : Slice U8, replacement.length = bytes.length →
          ExecutableInv view code (back (.Ok replacement)) ∧
          MemoryMutation view store (back (.Ok replacement)) address object ∧
          CumulativeStoreMutation view code store (back (.Ok replacement)) ∧
          (decodeStore view code (back (.Ok replacement))).MEMS =
            (decodeStore view code store).MEMS.set address.index.val
              ⟨(decodeMemory view object).TYPE, decodeBytes replacement.val⟩) ∧
        ∀ error, ExecutableInv view code (back (.Err error)) ∧
          CumulativeStoreMutation view code store (back (.Err error)) ⦄ := by
  unfold runtime.store.Store.memory_mut
  by_cases sameStore : address.store = store.id
  · simp only [bne_iff_ne, if_neg (not_not.mpr sameStore)]
    have position := issued sameStore
    let object := store.memories.val[address.index.val]
    have found : store.memories.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    rw [vec_index_mut_eq store.memories address.index object found]
    simp only [bind_ok, bind_tc_ok]
    obtain ⟨writeBack, borrowed, written⟩ := laws.write object.buf
    simp only [borrowed, bind_ok, WP.spec_ok, uncurry_apply_pair]
    have mutation (replacement : Slice U8) (sameLength : replacement.length = (view object.buf).length) :
        MemoryMutation view store
          {store with memories := store.memories.set address.index {object with buf := writeBack replacement}}
          address object := by
      exact ⟨writeBack replacement, rfl, by rw [written replacement sameLength]; exact sameLength⟩
    have cumulative (replacement : Slice U8) (sameLength : replacement.length = (view object.buf).length) :=
      memory_mutation_cumulative_of_shape view code store _ held.shape held.storeSyntax
        held.segmentBounds address object found (mutation replacement sameLength)
    refine ⟨object, sameStore, found, rfl, ?_, ?_⟩
    · intro replacement sameLength
      refine ⟨held.update (cumulative replacement sameLength), mutation replacement sameLength,
        cumulative replacement sameLength, ?_⟩
      simp only [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeMemory,
        written replacement sameLength, sameLength]
    · intro error
      exact ⟨held.update (cumulative (view object.buf) rfl), cumulative (view object.buf) rfl⟩
  · simp only [bne_iff_ne, if_pos sameStore, WP.spec_ok, uncurry_apply_pair]
    refine ⟨trivial, sameStore, ?_⟩
    intro reply
    exact ⟨held, CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds, trivial⟩

end Itasca.Integration

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Representation Itasca.Interp WebAssembly

theorem global_update_from_words {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (address : runtime.GlobalAddr) (value : runtime.Value)
    (mutation : GlobalMutation before after (sourceValue value))
    (old : runtime.store.GlobalInst) (found : before.globals.val[address.index.val]? = some old)
    (mutable : old.ty.mutability = .Var) (typed : old.ty.valtype = rawType value)
    (written : (decodeStore view code after).GLOBALS = (decodeStore view code before).GLOBALS.set address.index.val
      ⟨.mk_globaltype (Itasca.Translation.mutability old.ty.mutability) (Itasca.Translation.valueType old.ty.valtype),sourceValue value⟩) :
    GlobalUpdate (decodeStore view code before) (decodeStore view code after) address.index.val (sourceValue value) := by
  have frame : decodeStore view code after =
      {decodeStore view code before with GLOBALS := (decodeStore view code after).GLOBALS} := by
    obtain ⟨index,old,lo,hi,_,_,_,_,_,rfl⟩ := mutation
    rfl
  refine ⟨decodeGlobal old,?_,?_,?_⟩
  · simp only [decodeStore,List.getElem?_map,found,Option.map_some]
  · simp only [decodeGlobal,mutable,Itasca.Translation.mutability,typed,source_value_type]
  · rw [frame,written]
    rfl

theorem table_update_from_words {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before : runtime.store.Store M) (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (old : runtime.store.TableInst) (words : U64 × U64)
    (owned : ValueInStore before value)
    (found : before.tables.val[address.index.val]? = some old) (inside : index.val < old.elements.length)
    (typed : elementValueType old.ty = rawType value) (encoded : runtime.value.encode value = .ok words) :
    TableUpdate (decodeStore view code before)
      (decodeStore view code {before with tables := before.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}})
      address.index.val index.val (sourceValue value) := by
  have decoded := decode_encoded_value before value owned words encoded
  rw [←typed] at decoded
  refine ⟨decodeTable old,decodeRef old.ty words.1,?_,?_,?_,?_,?_⟩
  · simp only [decodeStore,List.getElem?_map,found,Option.map_some]
  · simpa only [decodeTable,List.length_map] using inside
  · cases kind : old.ty <;> simpa only [kind,elementValueType,decodeWords,ref_val_eq] using decoded
  · simp only [decodeTable,source_value_type,←typed]
    cases old.ty <;> rfl
  · simp only [decode_store_table_update,alloc.vec.Vec.set_val_eq,List.map_set,decodeTable,
      alloc.vec.Vec.length,List.length_set,U32.cast_Usize_val_eq]
    rfl

theorem memory_update_from_buffer {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (address : runtime.MemoryAddr) (old : runtime.store.MemInst M)
    (bytes : List byte) (found : before.memories.val[address.index.val]? = some old)
    (length : bytes.length = (view old.buf).length)
    (mutation : MemoryMutation view before after address old)
    (written : (decodeStore view code after).MEMS = (decodeStore view code before).MEMS.set address.index.val
      ⟨(decodeMemory view old).TYPE,bytes⟩) :
    MemoryUpdate (decodeStore view code before) (decodeStore view code after) address.index.val bytes := by
  have frame : decodeStore view code after =
      {decodeStore view code before with MEMS := (decodeStore view code after).MEMS} := by
    obtain ⟨buffer,rfl,_⟩ := mutation
    rfl
  refine ⟨decodeMemory view old,?_,?_,?_⟩
  · simp only [decodeStore,List.getElem?_map,found,Option.map_some]
  · simpa only [decodeMemory,decodeBytes,List.length_map] using length
  · rw [frame,written]

end Itasca.Store

end
