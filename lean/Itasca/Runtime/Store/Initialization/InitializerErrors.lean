import Itasca.Runtime.Store.Initialization.SegmentObjectEffects
import Itasca.Runtime.Store.Initialization.SegmentLoop
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses

/-!
Sections, each formerly its own module: SegmentInstructionShape, InitializerErrors.
-/

/-! ## SegmentInstructionShape -/

section

/-!
Store shape through segment initializer instructions. Bulk-operation shape preservation combines with ordinary instruction cases to retain the store invariant.
-/

/-! ## Segment Shape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem segment_bulk_shape {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ slots.length)
    (ready : SegmentBulkReady store inst code instruction)
    (compatible : SegmentBulkCompatible store inst code instruction) (shape : Shape view store) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => Shape view out.2 ∧ SegmentTypes store out.2 ⦄ := by
  cases ready with
  | memory data address target mapped issued mappedMemory issuedMemory =>
    have capacity := capacity ⟨data, Or.inl rfl⟩
    change 3 ≤ slots.val.length at capacity
    have slot0 : slots.val[0]? = some slots.val[0] := List.getElem?_eq_getElem (by omega)
    have slot1 : slots.val[1]? = some slots.val[1] := List.getElem?_eq_getElem (by omega)
    have slot2 : slots.val[2]? = some slots.val[2] := List.getElem?_eq_getElem (by omega)
    apply WP.spec_mono (bulk_memory_init memory view laws store instIndex function slots inst data address target
      store.memories.val[target.index.val] store.datas.val[address.val] _ _ _ found mapped
      (List.getElem?_eq_getElem issued) mappedMemory (List.getElem?_eq_getElem issuedMemory) slot0 slot1 slot2)
    intro out effect
    exact ⟨effect.shape shape (List.getElem?_eq_getElem issuedMemory), effect.types⟩
  | table entry element tableId address target descriptor mapped issued mappedTable issuedTable =>
    have capacity := capacity ⟨entry, Or.inr rfl⟩
    change 3 ≤ slots.val.length at capacity
    have slot0 : slots.val[0]? = some slots.val[0] := List.getElem?_eq_getElem (by omega)
    have slot1 : slots.val[1]? = some slots.val[1] := List.getElem?_eq_getElem (by omega)
    have slot2 : slots.val[2]? = some slots.val[2] := List.getElem?_eq_getElem (by omega)
    apply WP.spec_mono (bulk_table_init memory store instIndex function slots inst code entry element tableId address target
      store.tables.val[target.index.val] store.elems.val[address.val] _ _ _ found functionFound descriptor mapped
      (List.getElem?_eq_getElem issued) mappedTable (List.getElem?_eq_getElem issuedTable) slot0 slot1 slot2)
    intro out effect
    have typed := compatible element tableId address target store.elems.val[address.val] store.tables.val[target.index.val]
      descriptor mapped mappedTable (List.getElem?_eq_getElem issued) (List.getElem?_eq_getElem issuedTable)
    have references := shape.elements store.elems.val[address.val] (by simp)
    rw [typed] at references
    exact ⟨effect.shape shape (List.getElem?_eq_getElem issuedTable) references,
      effect.types (List.getElem?_eq_getElem issuedTable)⟩
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop memory store instIndex function 0#usize slots inst data address found mapped issued)
    rintro out rfl
    exact ⟨shape.data_drop address, ⟨rfl, rfl⟩⟩
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop memory store instIndex function 0#usize slots inst element address found mapped issued)
    rintro out rfl
    exact ⟨shape.element_drop address _, .element_drop store address _ (List.getElem?_eq_getElem issued)⟩


end Itasca.Runtime.Store

end

/-! ## Segment Instruction Shape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

/-- Both checked postconditions concern the same normally returned extracted
result. This combines refinements without assuming a second execution. -/
theorem segment_specs_and {T : Type} {call : Result T} {P Q : T → Prop}
    (first : call ⦃ P ⦄) (second : call ⦃ Q ⦄) : call ⦃ out => P out ∧ Q out ⦄ := by
  obtain ⟨out, returned, hp⟩ := WP.spec_imp_exists first
  rw [returned, WP.spec_ok] at second ⊢
  exact ⟨hp, second⟩

theorem segment_instruction_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction)
    (compatible : SegmentBulkCompatible store inst code instruction) (shape : Shape view store) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => Shape view out.2.2.1 ∧ SegmentTypes store out.2.2.1 ⦄ := by
  cases ready with
  | constant dst bits bound =>
    apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
      inst code dst bits found functionFound frames fetched pcBound bound)
    rintro out ⟨success, next, nextValue, effect, rfl, rfl⟩
    exact ⟨shape, .refl _⟩
  | global index addr value mapped issued capacity =>
    apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
      inst code _ [value.lo] found functionFound (.global index addr value mapped issued)
      (by simpa using capacity) frames fetched pcBound)
    rintro out ⟨success, slots, next, nextValue, frames, rfl, rfl⟩
    exact ⟨shape, .refl _⟩
  | bulk instruction ready capacity =>
    apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position
      inst code instruction ready.kind found functionFound frames fetched pcBound _
      (segment_bulk_shape memory view laws store instIndex function (alloc.vec.Vec.deref exec.slots)
        inst code instruction found functionFound (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using capacity)
        ready compatible shape))
    rintro out ⟨next, nextValue, effect, rfl, shape, types⟩
    exact ⟨shape, types⟩
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success, slots, empty, rfl, rfl⟩
    exact ⟨shape, .refl _⟩

end Itasca.Runtime.Store

end

end

/-! ## InitializerErrors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem eval_const_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → ((words[0]?).getD 0#u64).val ≤ Usize.max) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ value, out.1 = .Ok value → Interp.rawType value = ty ∧
          Interp.sourceValue value = decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → ∃ resource, error = .Exhausted resource) ⦄ := by
  unfold runtime.interp.eval_const
  step with Interp.synthetic_resolved_initializer_errors memory hooks floats allocator law store platform
    instIndex function inst code expr ty words hi hc compiled resolved
    as ⟨result, store', platform', hs, hp, success, errors⟩
  subst store' platform'
  cases result with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using errors error rfl
  | Ok pair =>
    have hpair := success pair rfl
    subst pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.decode_value_boundary ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
      store.id referenceBound as ⟨value, hty, hvalue⟩
    simp_all

end Itasca.Runtime.Store

end
