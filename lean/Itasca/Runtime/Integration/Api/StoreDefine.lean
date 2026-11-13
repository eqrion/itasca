import Itasca.Runtime.Integration.Api.StoreCreate

/-! Public store definitions preserve executable certificates and expose the
exact appended object or unchanged store on failure. -/

namespace Itasca.Runtime.Integration
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
      ExecutableInv view code after ∧ Interp.FrameStoreMetadata store after ∧
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
      exact ⟨held, Interp.FrameStoreMetadata.refl store, trivial, trivial, trivial⟩
    · simp only [ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have available : store.externs.length < Usize.max := by
        unfold objectCount at space
        scalar_tac
      step as ⟨externs, appended⟩
      refine ⟨held.append_extern identity externs appended space, ⟨rfl, rfl, rfl, rfl⟩,
        rfl, rfl, ?_, externs, appended, rfl⟩
      · simp only [ValueInStore, Interp.ValueOwnedFits, alloc.vec.Vec.len_val,
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
    exact ⟨held, Interp.FrameStoreMetadata.refl store, trivial, trivial, trivial⟩

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
        SpecExt.HostFunction (decodeStore view code after) address.index.val host.val
          (ty.params.val.map Interp.sourceType) (ty.results.val.map Interp.sourceType) ⦄ := by
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
        ExternalIssued after (.Global address) ∧ ty.valtype = Interp.rawType value ∧
        (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS ++
          [⟨.mk_globaltype (decodeMut ty.mutability) (Interp.sourceType ty.valtype),
            Interp.sourceValue value⟩] ⦄ := by
  classical
  have bound : objectCount store ≤ Usize.max := by
    have limited := held.shape.object_count_bound
    scalar_tac
  by_cases accepted : Interp.OwnedBy store.id value ∧ ty.valtype = Interp.rawType value
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
            ty.valtype (Interp.rawType value) = .ok true) := by
      obtain ⟨checked, run, same⟩ := WP.spec_imp_exists (Interp.check_value_eq memory store value)
      subst checked
      by_cases owner : Interp.OwnedBy store.id value
      · right
        refine ⟨?_, ?_⟩
        · simpa only [Interp.checkOwner, if_pos owner] using run
        · have mismatch : ty.valtype ≠ Interp.rawType value := fun same => accepted ⟨owner, same⟩
          rw [Interp.value_type_ne_eq, if_neg mismatch]
      · left
        exact ⟨.WrongStore, by simpa only [Interp.checkOwner, if_neg owner] using run⟩
    step with define_global_rejected memory allocator store ty value bound rejected
      as ⟨result, after, error, failed, unchanged⟩
    subst result after
    exact ⟨held, ⟨.refl _, rfl, held.shape, held.segmentBounds,
      Spec.extend_store_refl _ held.well_formed, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

end Itasca.Runtime.Integration
