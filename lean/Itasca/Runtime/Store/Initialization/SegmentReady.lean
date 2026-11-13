import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Interp.Relations.SourceClosure

/-!
Sections, each formerly its own module: BulkPreservation, SegmentStep, SegmentReady.
-/

/-! ## BulkPreservation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem copy_segment_all (predicate : U64 → Prop) (before source : List U64)
    (dst src count : Nat) (sourceBound : src + count ≤ source.length)
    (old : ∀ word ∈ before, predicate word) (input : ∀ word ∈ source, predicate word) :
    ∀ word ∈ copySegment before source dst src count, predicate word := by
  induction count with
  | zero => exact old
  | succ n ih =>
    intro word member
    simp only [copySegment] at member
    rcases List.mem_or_eq_of_mem_set member with previous | changed
    · exact ih (by omega) word previous
    · subst word
      have bound : src + n < source.length := by omega
      exact input _ (by simp [bound])

theorem TableInitializationEffect.shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {tableIndex : Usize} {table : runtime.store.TableInst}
    {segment : runtime.store.ElemInst} {destination source count : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.store.Store M}
    (effect : TableInitializationEffect store tableIndex table segment destination source count out)
    (shape : Shape view store) (target : store.tables.val[tableIndex.val]? = some table)
    (references : ∀ word ∈ segment.refs.val, ReferenceShape store table.ty word) : Shape view out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · rename_i fits
    obtain ⟨words, rfl, values⟩ := effect
    have bound := (List.getElem?_eq_some_iff.mp target).1
    have read := (List.getElem?_eq_some_iff.mp target).2
    have old := shape.tables table (List.mem_of_getElem? target)
    have length : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using (congrArg List.length values).trans (copy_segment_length _ _ _ _ _)
    apply shape.table_replace_same_length tableIndex bound {table with elements := words}
    · refine ⟨by simpa [length] using old.1, ?_, ?_⟩
      · simpa [length] using old.2.1
      · intro word member
        rw [values] at member
        exact copy_segment_all (ReferenceShape store table.ty) _ _ _ _ _ fits.2 old.2.2 references word member
    · simpa only [read] using length
  · rw [effect]
    exact shape

theorem MemoryInitializationEffect.shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {memoryIndex : Usize} {memory : runtime.store.MemInst M}
    {segment : runtime.store.DataInst} {destination source count : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.store.Store M}
    (effect : MemoryInitializationEffect view store memoryIndex memory segment destination source count out)
    (shape : Shape view store) (target : store.memories.val[memoryIndex.val]? = some memory) : Shape view out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, values⟩ := effect
    have bound := (List.getElem?_eq_some_iff.mp target).1
    have read := (List.getElem?_eq_some_iff.mp target).2
    apply shape.memory_replace_same_length memoryIndex bound {memory with buf := buffer}
    · have lengths := congrArg List.length values
      simpa only [List.length_setSlice!, read] using lengths
    · simp only [read]
  · rw [effect]
    exact shape

theorem Shape.data_drop {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (address : Usize) :
    Shape view {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩} := by
  constructor
  · exact shape.identity
  · simpa [FunctionShape] using shape.functions
  · exact shape.memories
  · simpa [TableShape, ReferenceShape] using shape.tables
  · simpa [GlobalShape, ReferenceShape] using shape.globals
  · simpa [ReferenceShape] using shape.elements
  · simpa [InstanceShape] using shape.instances
  · exact shape.canonicalTypes
  · exact shape.objectLimit
  · exact shape.instanceLimit
  · exact shape.instanceAccounting
  · exact shape.instanceItemLimit
  · exact shape.signatureAccounting
  · exact shape.signatureLimit
  · exact shape.memoryAccounting
  · exact shape.memoryLimit
  · exact shape.tableAccounting
  · exact shape.tableLimit

theorem Shape.element_drop {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (address : Usize) (segment : runtime.store.ElemInst) :
    Shape view {store with elems := store.elems.set address {segment with refs := alloc.vec.Vec.new U64}} := by
  have elements : ∀ e ∈ (store.elems.set address {segment with refs := alloc.vec.Vec.new U64}).val,
      ∀ word ∈ e.refs.val, ReferenceShape store e.ty word := by
    intro e member
    simp only [alloc.vec.Vec.set_val_eq] at member
    rcases List.mem_or_eq_of_mem_set member with previous | changed
    · exact shape.elements e previous
    · subst e; simp
  constructor
  · exact shape.identity
  · simpa [FunctionShape] using shape.functions
  · exact shape.memories
  · simpa [TableShape, ReferenceShape] using shape.tables
  · simpa [GlobalShape, ReferenceShape] using shape.globals
  · simpa [ReferenceShape] using elements
  · simpa [InstanceShape] using shape.instances
  · exact shape.canonicalTypes
  · exact shape.objectLimit
  · exact shape.instanceLimit
  · exact shape.instanceAccounting
  · exact shape.instanceItemLimit
  · exact shape.signatureAccounting
  · exact shape.signatureLimit
  · exact shape.memoryAccounting
  · exact shape.memoryLimit
  · exact shape.tableAccounting
  · exact shape.tableLimit

end Itasca.Runtime.Store

end

/-! ## SegmentStep -/

section

/-! Straight-line initialization steps reuse the actual interpreter fetch and
dispatch path, with exact program-counter and metadata effects. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem segment_step_read (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots.val = initialSlots exec.slots.val words ∧
      ∃ next : U32, next.val = position.val + 1 ∧ out.2.1.frames.val = [initializerFrame instIndex function next] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code instruction
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simpa [initializerFrame] using pcBound)
  intro next hnext
  apply WP.spec_mono (dispatch_initial_read memory hooks floats allocator
    { exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next) }
    store platform instIndex function 0#usize inst code instruction words hi hc read capacity)
  rintro out ⟨hok, ⟨hslots, hrest⟩, hs, hp⟩
  have hframes := congrArg runtime.interp.Execution.frames hrest
  exact ⟨hok, hslots, next, hnext, by simpa [hf] using congrArg alloc.vec.Vec.val hframes, hs, hp⟩


/-- Administrative bulk dispatch preserves the entire execution record and
passes through precisely the ordinary success/trap result of the checked bulk
handler. This is a composition rule, not a machine-correctness premise. -/
theorem segment_execute_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (inst function base : Usize)
    (instruction : runtime.bytecode.Instr)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store inst function base
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.execute_bulk memory exec store inst function base instruction
      ⦃ out => out.2.1 = exec ∧ post (out.1, out.2.2) ⦄ := by
  unfold runtime.interp.execute_bulk
  step with bulk as ⟨result, after, effect⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

inductive SegmentBulk : runtime.bytecode.Instr → Prop where
  | memory (data : U32) : SegmentBulk (.MemoryInit 0#u32 data)
  | table (entry : U32) : SegmentBulk (.TableInit 0#u32 entry)
  | dataDrop (data : U32) : SegmentBulk (.DataDrop data)
  | elementDrop (element : U32) : SegmentBulk (.ElemDrop element)

theorem segment_dispatch_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex inst function : Usize)
    (instruction : runtime.bytecode.Instr) (kind : SegmentBulk instruction)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store inst function 0#usize
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      inst function 0#usize instruction
      ⦃ out => out.2.1 = exec ∧ out.2.2.2 = platform ∧ post (out.1, out.2.2.1) ⦄ := by
  cases kind <;> simp only [runtime.interp.dispatch] <;>
    step with segment_execute_bulk memory exec store inst function 0#usize _ post bulk <;>
    simp_all

theorem segment_step_return (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (width : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (capacity : width.val ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some (.Return 0#u32 width))
    (pcBound : position.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots = exec.slots ∧ out.2.1.frames.val = [] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code (.Return 0#u32 width)
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simpa [initializerFrame] using pcBound)
  intro pc hpc
  simp only [runtime.interp.dispatch, initializerFrame]
  step with initializer_return_effect
    { exec with frames := exec.frames.set 0#usize { «instance» := instIndex, function := function, pc := pc, base := 0#usize } }
    width capacity
  simp_all [hf]


theorem segment_step_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (kind : SegmentBulk instruction)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store instIndex function 0#usize
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ next : U32, next.val = position.val + 1 ∧
        out.2.1 = {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)} ∧
        out.2.2.2 = platform ∧ post (out.1, out.2.2.1) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code instruction
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop
    (by simpa [initializerFrame] using pcBound)
  intro next hnext
  apply WP.spec_mono (segment_dispatch_bulk memory hooks floats allocator
    {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
    store platform 0#usize instIndex function instruction kind post bulk)
  intro out effect
  exact ⟨next, hnext, effect⟩

theorem segment_step_const32 (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (dst bits : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some (.Const32 dst bits))
    (pcBound : position.val < U32.max) (capacity : dst.val < exec.slots.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ∃ next : U32, next.val = position.val + 1 ∧
        SlotsEffect {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
          out.2.1 (exec.slots.val.set dst.val (UScalar.cast .U64 bits)) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code (.Const32 dst bits)
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop
    (by simpa [initializerFrame] using pcBound)
  intro next hnext
  simp only [runtime.interp.dispatch, initializerFrame]
  have effect := const32_effect
    {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
    0#usize dst bits (by simpa using capacity)
  simp only [initializerFrame] at effect
  step with effect as ⟨status, after, success, slots⟩
  simp only [Nat.zero_add] at slots
  simpa only [success, true_and, and_true, initializerFrame] using (show ∃ next : U32, next.val = position.val + 1 ∧ SlotsEffect {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)} after (exec.slots.val.set dst.val (UScalar.cast .U64 bits)) from ⟨next, hnext, slots⟩)

end Itasca.Runtime.Store

end

/-! ## SegmentReady -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Segment execution changes buffers, table words and dropped-segment contents,
but preserves the address spaces and every constant-read/code lookup. -/
structure SegmentAddressSpace {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs = before.funcs
  signatures : after.types = before.types
  globals : after.globals = before.globals
  instances : after.instances = before.instances
  tables : after.tables.length = before.tables.length
  memories : after.memories.length = before.memories.length
  elements : after.elems.length = before.elems.length
  datas : after.datas.length = before.datas.length
  frozen : after = {before with tables := after.tables, memories := after.memories, elems := after.elems, datas := after.datas}

theorem SegmentAddressSpace.refl {M : Type} (store : runtime.store.Store M) :
    SegmentAddressSpace store store := by constructor <;> rfl

theorem SegmentAddressSpace.trans {M : Type} {a b c : runtime.store.Store M}
    (ab : SegmentAddressSpace a b) (bc : SegmentAddressSpace b c) : SegmentAddressSpace a c := by
  constructor
  all_goals first
    | exact bc.identity.trans ab.identity
    | exact bc.functions.trans ab.functions
    | exact bc.signatures.trans ab.signatures
    | exact bc.globals.trans ab.globals
    | exact bc.instances.trans ab.instances
    | exact bc.tables.trans ab.tables
    | exact bc.memories.trans ab.memories
    | exact bc.elements.trans ab.elements
    | exact bc.datas.trans ab.datas
    | rw [bc.frozen, ab.frozen]

/-- Issued indices required by the four emitted bulk instruction forms. Buffer
range bounds are deliberately absent: their failure is an ordinary Wasm trap. -/
inductive SegmentBulkReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → Prop where
  | memory (data : U32) (address : Usize) (memory : runtime.MemoryAddr)
      (mapped : inst.datas.val[data.val]? = some address) (issued : address.val < store.datas.length)
      (mappedMemory : inst.memories.val[0]? = some memory) (issuedMemory : memory.index.val < store.memories.length) :
      SegmentBulkReady store inst code (.MemoryInit 0#u32 data)
  | table (entry element tableId : U32) (address : Usize) (table : runtime.TableAddr)
      (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
      (mapped : inst.elems.val[element.val]? = some address) (issued : address.val < store.elems.length)
      (mappedTable : inst.tables.val[tableId.val]? = some table) (issuedTable : table.index.val < store.tables.length) :
      SegmentBulkReady store inst code (.TableInit 0#u32 entry)
  | dataDrop (data : U32) (address : Usize)
      (mapped : inst.datas.val[data.val]? = some address) (issued : address.val < store.datas.length) :
      SegmentBulkReady store inst code (.DataDrop data)
  | elementDrop (element : U32) (address : Usize)
      (mapped : inst.elems.val[element.val]? = some address) (issued : address.val < store.elems.length) :
      SegmentBulkReady store inst code (.ElemDrop element)

theorem SegmentBulkReady.kind {M : Type} {store : runtime.store.Store M} {inst code instruction}
    (ready : SegmentBulkReady store inst code instruction) : SegmentBulk instruction := by
  cases ready <;> constructor

theorem SegmentBulkReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code instruction} (ready : SegmentBulkReady store inst code instruction)
    (same : SegmentAddressSpace store after) : SegmentBulkReady after inst code instruction := by
  cases ready with
  | memory data address memory mapped issued mappedMemory issuedMemory =>
    exact .memory data address memory mapped (same.datas.symm ▸ issued) mappedMemory (same.memories.symm ▸ issuedMemory)
  | table entry element tableId address table descriptor mapped issued mappedTable issuedTable =>
    exact .table entry element tableId address table descriptor mapped (same.elements.symm ▸ issued)
      mappedTable (same.tables.symm ▸ issuedTable)
  | dataDrop data address mapped issued => exact .dataDrop data address mapped (same.datas.symm ▸ issued)
  | elementDrop element address mapped issued => exact .elementDrop element address mapped (same.elements.symm ▸ issued)

def SegmentStatus (result : core.result.Result Unit runtime.ExecError) : Prop :=
  result = .Ok () ∨ result = .Err (.Trap .MemoryOutOfBounds) ∨ result = .Err (.Trap .TableOutOfBounds)

private theorem memory_effect_metadata {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out) :
    SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, _⟩ := effect
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  · rw [effect]
    exact ⟨Or.inr (Or.inl rfl), .refl store⟩

private theorem table_effect_metadata {M : Type} {store : runtime.store.Store M}
    {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out) :
    SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, _⟩ := effect
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  · rw [effect]
    exact ⟨Or.inr (Or.inr rfl), .refl store⟩

theorem segment_bulk_total {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ slots.length)
    (ready : SegmentBulkReady store inst code instruction) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 ⦄ := by
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
    exact memory_effect_metadata effect
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
    exact table_effect_metadata effect
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop memory store instIndex function 0#usize slots inst data address found mapped issued)
    rintro out rfl
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop memory store instIndex function 0#usize slots inst element address found mapped issued)
    rintro out rfl
    constructor
    · exact Or.inl rfl
    · constructor <;> simp

end Itasca.Runtime.Store

end
