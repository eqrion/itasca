import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Store.Api.GlobalStagingAndCopy
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Spec.PrimitiveOperations
import ItascaRust.Funs
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Proofs for Runtime / Store / Preparation.

This module collects PreparationResults, AllocationTableMemory, PreparationErrorLoops.
Each section documents its contracts and consumers.
-/

/-! ## PreparationResults -/

section

/-! ## StagingAddresses -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.owners {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    (owners : ∀ address ∈ inst.tables.val, address.store = store.id) :
    ∀ address ∈ out.2.2.tables.val, address.store = out.2.1.id := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact owners
  · intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact owners address old
    · rfl

theorem MemoryStageEffect.owners {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    (owners : ∀ address ∈ inst.memories.val, address.store = store.id) :
    ∀ address ∈ out.2.2.memories.val, address.store = out.2.1.id := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact owners
  · intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact owners address old
    · rfl

theorem GlobalStageEffect.addresses {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    (issued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length) :
    ∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact issued
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    have size : globals.length = store.globals.length + 1 := by simpa using congrArg List.length stored
    rcases member with old | rfl
    · obtain ⟨owner, previous⟩ := issued address old
      exact ⟨owner, by simp only [size]; omega⟩
    · exact ⟨rfl, by simp [size]⟩

theorem DataStageEffect.addresses {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    (issued : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    ∀ address ∈ next.datas.val, address.val < after.datas.length := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact issued
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    have size : datas.length = store.datas.length + 1 := by simpa using congrArg List.length stored
    rcases member with old | rfl
    · have previous := issued address old
      simp only [size]
      omega
    · simp [size]

end Itasca.Store

end

/-! ## PreparationResults -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem type_parts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) (i j : runtime.store.ModuleInst) :
    typeParts a s i = typeParts b t j ↔ a = b ∧ s = t ∧ i = j := by
  cases i; cases j
  simp [typeParts]

/-- Normalize the flattened tuple returned by the actual preparation loops.
The computation and its checked total postcondition remain explicit. -/
theorem preparation_result {M R : Type}
    (parts : runtime.store.Store M → core.result.Result Unit runtime.ExecError → runtime.store.ModuleInst → R)
    (injective : ∀ a b s t i j, parts a s i = parts b t j → a = b ∧ s = t ∧ i = j)
    (computation : Result R) (post : runtime.store.Store M → runtime.store.ModuleInst → core.result.Result Unit runtime.ExecError → Prop)
    (checked : computation ⦃ out => ∃ store inst status, out = parts store status inst ∧ post store inst status ⦄)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (run : computation = .ok (parts store status inst)) : post store inst status := by
  rw [run] at checked
  simp only [WP.spec_ok] at checked
  obtain ⟨after, next, result, eq, property⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := injective _ _ _ _ _ _ eq
  exact property

end Itasca.Store

end

end

/-! ## AllocationTableMemory -/

section

open Itasca.Representation

/-!
# Decoded allocation suffixes

Table and memory staging decode to the corresponding slices of the source allocation sequence. Preparation uses these exact suffixes when assembling its decoded store.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

theorem decode_table_allocation (ty : wasm_types.TableType) (elements : alloc.vec.Vec U64)
    (zeros : elements.val = List.replicate ty.limits.min.val 0#u64) :
    decodeTable {elements, ty := ty.elem, maximum := ty.limits.max} =
      Spec.allocationTable (Translation.Environment.tableType ty) := by
  simp [decodeTable, alloc.vec.Vec.length, zeros, List.length_replicate, List.map_replicate,
    decodeRef, ↓reduceIte, decode_elem_type_source,
    Spec.allocationTable, Translation.Environment.tableType, Translation.Environment.limitsType, decodeLimits]

theorem decode_memory_allocation {M : Type} (view : M → Slice U8) (ty : wasm_types.MemType) (buffer : M)
    (zeros : (view buffer).val = List.replicate (ty.limits.min.val * 65536) 0#u8) :
    decodeMemory view {buf := buffer, maximum := ty.limits.max} =
      Spec.allocationMemory (Translation.Environment.memType ty) := by
  simp only [decodeMemory, Slice.length, zeros, List.length_replicate, decodeBytes,
    List.map_replicate, Spec.allocationMemory, Translation.Environment.memType,
    Translation.Environment.limitsType, decodeLimits]
  norm_num [Ki]

theorem TableStageEffect.decoded {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out}
    (effect : TableStageEffect store inst ty out) (success : out.1 = .Ok ()) :
    out.2.1.tables.val.map decodeTable = store.tables.val.map decodeTable ++
      [Spec.allocationTable (Translation.Environment.tableType ty)] := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · cases success
  · simp only [appended, List.map_append, List.map_singleton, decode_table_allocation ty elements zeros]

theorem MemoryStageEffect.decoded {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out}
    (effect : MemoryStageEffect view store inst ty out) (success : out.1 = .Ok ()) :
    out.2.1.memories.val.map (decodeMemory view) = store.memories.val.map (decodeMemory view) ++
      [Spec.allocationMemory (Translation.Environment.memType ty)] := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · cases success
  · simp only [appended, List.map_append, List.map_singleton, decode_memory_allocation view ty buffer zeros]
end Itasca.Store

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The decoded suffix allocated so far corresponds exactly to a source slice. -/
def AllocationPrefix {T U : Type} (allocate : T → U) (source : List T)
    (start : Nat) (original actual : List U) (position : Nat) : Prop :=
  actual = original ++ ((source.take position).drop start).map allocate

theorem AllocationPrefix.initial {T U : Type} (allocate : T → U) (source : List T)
    (start : Nat) (original : List U) : AllocationPrefix allocate source start original original start := by
  simp [AllocationPrefix]

theorem AllocationPrefix.append {T U : Type} {allocate : T → U} {source : List T}
    {start position : Nat} {original actual : List U}
    (hprefix : AllocationPrefix allocate source start original actual position)
    (prior : start ≤ position) (bound : position < source.length) :
    AllocationPrefix allocate source start original (actual ++ [allocate source[position]]) (position + 1) := by
  unfold AllocationPrefix at *
  rw [List.take_succ_eq_append_getElem bound, List.drop_append_of_le_length (by simp; omega), List.map_append]
  simpa [hprefix, List.append_assoc]

theorem AllocationPrefix.complete {T U : Type} {allocate : T → U} {source : List T}
    {start : Nat} {original actual : List U}
    (hprefix : AllocationPrefix allocate source start original actual source.length) :
    actual = original ++ (source.drop start).map allocate := by
  simpa [AllocationPrefix] using hprefix
end Itasca.Store

end

/-! ## PreparationErrorLoops -/

section

open Itasca.Representation

/-! ## AllocationInitializers -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : GlobalStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended globals addresses global appended mapped canonical room =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · intro value member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [GlobalShape, ReferenceShape] using shape.globals value old
      · simpa only [GlobalShape, ReferenceShape] using canonical
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
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem ElementContentEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst source status} (effect : ElementContentEffect store index inst source status after)
    (shape : AllocationShape view store) : AllocationShape view after := by
  cases effect with
  | failed error => exact shape
  | appended elements addresses values appended mapped canonical =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · intro element member word contained
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [ReferenceShape] using shape.elements element old word contained
      · simpa only [ReferenceShape] using canonical word contained
    · exact shape.canonicalTypes
    · exact shape.objectLimit
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem DataStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended datas addresses data appended mapped =>
    cases shape
    constructor <;> assumption

end Itasca.Store

end

/-! ## PreparationErrorLoops -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Actual type staging preserves the resource-only error class. This is a
normal-return statement, so it does not assume any unchecked index is valid. -/
theorem type_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop3 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop3.body,
      runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := add_type_errors memory allocator law store inst index _ called
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop3, runtime.store.instantiate.Store.prepare_instance_loop3.body,
            runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

theorem function_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store status index inst instanceIndex = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop4 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop4.body,
      runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := add_function_errors memory allocator law store inst instanceIndex index _ called
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator nextStore nextStatus nextIndex nextInst instanceIndex = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop4, runtime.store.instantiate.Store.prepare_instance_loop4.body,
            runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed
end Itasca.Store

end

end
