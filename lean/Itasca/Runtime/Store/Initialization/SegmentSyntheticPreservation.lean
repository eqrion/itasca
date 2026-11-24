import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Local.Capacity.ConditionalAndSimdAvailability
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Interp.Relations.SourceClosure

/-!
Proofs for Runtime / Store / Initialization.

This module collects SegmentLoop, SegmentSyntheticPreservation.
Each section documents its contracts and consumers.
-/

/-! ## SegmentLoop -/

section

open Itasca.Representation

/-! ## SegmentInstruction -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- Syntactic and issued-address requirements of one initializer instruction.
There are no interpreter executions or semantic postconditions in this record. -/
inductive SegmentInstructionReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (width : Nat) :
    runtime.bytecode.Instr → Prop where
  | constant (dst bits : U32) (bound : dst.val < width) :
      SegmentInstructionReady store inst code width (.Const32 dst bits)
  | global (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
      (mapped : inst.globals.val[index.val]? = some addr)
      (issued : store.globals.val[addr.index.val]? = some value) (capacity : 1 ≤ width) :
      SegmentInstructionReady store inst code width (.GlobalGet 0#u32 index)
  | bulk (instruction : runtime.bytecode.Instr) (ready : SegmentBulkReady store inst code instruction)
      (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ width) :
      SegmentInstructionReady store inst code width instruction
  | done : SegmentInstructionReady store inst code width (.Return 0#u32 0#u32)

theorem SegmentInstructionReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code width instruction} (ready : SegmentInstructionReady store inst code width instruction)
    (same : SegmentAddressSpace store after) : SegmentInstructionReady after inst code width instruction := by
  cases ready with
  | constant dst bits bound => exact .constant dst bits bound
  | global index addr value mapped issued capacity =>
    exact .global index addr value mapped (by rw [same.globals]; exact issued) capacity
  | bulk instruction ready capacity => exact .bulk instruction (ready.transport same) capacity
  | done => exact .done

def segmentReturns : runtime.bytecode.Instr → Bool
  | .Return _ _ => true
  | _ => false

structure SegmentStepEffect {M P : Type} (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (platform : P) (instIndex function : Usize) (position : U32) (instruction : runtime.bytecode.Instr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop where
  status : SegmentStatus out.1
  slots : out.2.1.slots.length = exec.slots.length
  metadata : SegmentAddressSpace store out.2.2.1
  platform : out.2.2.2 = platform
  frames : if segmentReturns instruction then out.2.1.frames.val = [] else
    ∃ next : U32, next.val = position.val + 1 ∧ out.2.1.frames.val = [initializerFrame instIndex function next]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem segment_instruction_total (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => SegmentStepEffect exec store platform instIndex function position instruction out ⦄ := by
  cases ready with
  | constant dst bits bound =>
    apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
      inst code dst bits found functionFound frames fetched pcBound bound)
    rintro out ⟨success, next, nextValue, effect, rfl, rfl⟩
    refine ⟨Or.inl success, by simp only [alloc.vec.Vec.length, effect.1, List.length_set], .refl _, rfl, ?_⟩
    simp only [segmentReturns, Bool.false_eq_true, ↓reduceIte]
    refine ⟨next, nextValue, ?_⟩
    have same := congrArg (fun e : runtime.interp.Execution => e.frames.val) effect.2
    simpa [frames] using same
  | global index addr value mapped issued capacity =>
    apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
      inst code _ [value.lo] found functionFound (.global index addr value mapped issued)
      (by simpa using capacity) frames fetched pcBound)
    rintro out ⟨success, slots, next, nextValue, frames, rfl, rfl⟩
    refine ⟨Or.inl success, ?_, .refl _, rfl, ?_⟩
    · rw [alloc.vec.Vec.length, slots, initial_slots_length]
    · exact ⟨next, nextValue, frames⟩
  | bulk instruction ready capacity =>
    apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position
      inst code instruction ready.kind found functionFound frames fetched pcBound _
      (segment_bulk_total memory view laws store instIndex function (alloc.vec.Vec.deref exec.slots)
        inst code instruction found functionFound (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using capacity) ready))
    rintro out ⟨next, nextValue, effect, rfl, status, metadata⟩
    refine ⟨status, by rw [effect], metadata, rfl, ?_⟩
    have nonReturn : segmentReturns instruction = false := by cases ready <;> rfl
    simp only [nonReturn, Bool.false_eq_true, ↓reduceIte]
    rw [effect]
    exact ⟨next, nextValue, by simp [frames]⟩
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success, slots, empty, rfl, rfl⟩
    exact ⟨Or.inl success, by rw [slots], .refl _, rfl, by simpa [segmentReturns] using empty⟩

end Itasca.Store

end

/-! ## SegmentCertificate -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem offset_instruction_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (instruction : runtime.bytecode.Instr) (width : Nat)
    (typed : Itasca.Module.Constants.Valid inst.module.module.env expr .I32)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (emitted : Compiler.ConstantInstruction code 0#u32 expr .I32 instruction)
    (capacity : 1 ≤ width) : SegmentInstructionReady store inst code width instruction := by
  obtain ⟨words, resolved⟩ := initializer_resolves store inst expr .I32 typed bindings imports
  rcases Compiler.valid_offset_shape typed with ⟨bits, rfl⟩ | ⟨index, rfl⟩
  · cases emitted
    exact .constant _ _ (by simp; omega)
  · cases emitted
    cases resolved with
    | global ty index addr value mapped found typed scalar =>
      exact .global index addr value mapped found capacity

/-- A retained element block uses only indices already issued by staging. -/
theorem element_program_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Element) (instructions : List runtime.bytecode.Instr)
    (width : Nat) (program : Compiler.ElementProgram code index segment instructions)
    (sourceBound : index < inst.module.module.env.elements.length)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (typed : Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (capacity : instructions.length = 5 → 3 ≤ width) :
    ∀ instruction ∈ instructions, SegmentInstructionReady store inst code width instruction := by
  rcases shape with ⟨_, _, tableCount, _, _, elementCount, _, _, _, tables, _, _, elements, _⟩
  have localBound : index < inst.elems.val.length := by simp only [alloc.vec.Vec.length] at *; omega
  let address := inst.elems.val[index]
  have mapped : inst.elems.val[index]? = some address := List.getElem?_eq_getElem localBound
  have issued := elements address (List.mem_of_getElem? mapped)
  cases program with
  | passive mode => simp
  | declarative mode word encoded =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .bulk _ (.elementDrop word address (by simpa [encoded] using mapped) issued) (by simp)
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have room : 3 ≤ width := capacity (by simp)
    obtain ⟨tableBound, sameType, valid⟩ :=
      (show ∃ h : table.val < inst.module.module.env.table_types.val.length,
        inst.module.module.env.table_types.val[table.val].elem = segment.elem ∧
        Itasca.Module.Constants.Valid inst.module.module.env offset .I32 from by simpa [mode] using typed.1)
    have localTableBound : table.val < inst.tables.val.length := by
      simp only [alloc.vec.Vec.length] at tableCount
      omega
    let target := inst.tables.val[table.val]
    have tableMapped : inst.tables.val[table.val]? = some target := List.getElem?_eq_getElem localTableBound
    have tableIssued := (tables target (List.mem_of_getElem? tableMapped)).2
    have ready := offset_instruction_ready store inst code offset instruction width valid imports bindings constant (by omega)
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ready
    · exact .constant _ _ (by simp; omega)
    · exact .constant _ _ (by simp; omega)
    · exact .bulk _ (.table entry word table address target descriptor (by simpa [encoded] using mapped) issued tableMapped tableIssued) (fun _ => room)
    · exact .bulk _ (.elementDrop word address (by simpa [encoded] using mapped) issued) (by simp)

/-- Data-block safety needs a present memory, not a successful range check. -/
theorem data_program_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Data) (instructions : List runtime.bytecode.Instr)
    (width : Nat) (program : Compiler.DataProgram code index segment instructions)
    (sourceBound : index < inst.module.module.tail.data.length)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (typed : Itasca.Module.Data.Valid inst.module.module.env segment)
    (capacity : instructions.length = 5 → 3 ≤ width) :
    ∀ instruction ∈ instructions, SegmentInstructionReady store inst code width instruction := by
  rcases shape with ⟨_, _, _, memoryCount, _, _, dataCount, _, _, _, memories, _, _, datas⟩
  have localBound : index < inst.datas.val.length := by simp only [alloc.vec.Vec.length] at *; omega
  let address := inst.datas.val[index]
  have mapped : inst.datas.val[index]? = some address := List.getElem?_eq_getElem localBound
  have issued := datas address (List.mem_of_getElem? mapped)
  cases program with
  | passive mode => simp
  | active memory offset mode word length encoded count instruction constant =>
    have room : 3 ≤ width := capacity (by simp)
    obtain ⟨memoryBound, valid⟩ :=
      (show memory.val < inst.module.module.env.mem_types.val.length ∧
        Itasca.Module.Constants.Valid inst.module.module.env offset .I32 from by simpa [Itasca.Module.Data.Valid, mode] using typed)
    have localMemoryBound : 0 < inst.memories.val.length := by
      simp only [alloc.vec.Vec.length] at memoryCount
      omega
    let target := inst.memories.val[0]
    have memoryMapped : inst.memories.val[0]? = some target := List.getElem?_eq_getElem localMemoryBound
    have memoryIssued := (memories target (List.mem_of_getElem? memoryMapped)).2
    have ready := offset_instruction_ready store inst code offset instruction width valid imports bindings constant (by omega)
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ready
    · exact .constant _ _ (by simp; omega)
    · exact .constant _ _ (by simp; omega)
    · exact .bulk _ (.memory word address target (by simpa [encoded] using mapped) issued memoryMapped memoryIssued) (fun _ => room)
    · exact .bulk _ (.dataDrop word address (by simpa [encoded] using mapped) issued) (by simp)

end Itasca.Store

end

/-! ## SegmentLoop -/

section

/-!
Ready segment bytecode and total loop execution. Readiness transport and the next-instruction bound justify each iteration and the decreasing remaining-code measure.
-/

/-! ## Segment Code Ready -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- A finite straight-line initialization body. Every instruction carries only
syntactic bounds and issued-address facts, and the final instruction returns. -/
structure SegmentCodeReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (width : Nat) : Prop where
  size : code.code.length < U32.max
  returnLast : code.code.val.getLast? = some (.Return 0#u32 0#u32)
  instructions : ∀ instruction ∈ code.code.val, SegmentInstructionReady store inst code width instruction

theorem SegmentCodeReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code width} (ready : SegmentCodeReady store inst code width)
    (metadata : SegmentAddressSpace store after) : SegmentCodeReady after inst code width :=
  ⟨ready.size, ready.returnLast, fun instruction member => (ready.instructions instruction member).transport metadata⟩

theorem segment_program_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (program : Compiler.SegmentProgram inst.module code)
    (pcBound : code.code.length < U32.max)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (elementsValid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (dataValid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.Module.Data.Valid inst.module.module.env segment) :
    SegmentCodeReady store inst code code.slot_count.val := by
  obtain ⟨elements, datas, certificate⟩ := program
  refine ⟨pcBound, by rw [certificate.instructions]; simp, ?_⟩
  intro instruction member
  rw [certificate.instructions] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.env.elements.val.length := by
      have := certificate.elementCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.env.elements.val[index]
    have found : inst.module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.elements index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    apply element_program_ready store inst code index segment block code.slot_count.val emitted sourceBound shape imports bindings
      (elementsValid segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro length
    have cap := certificate.activeCapacity (Or.inl ⟨index, block, by rw [List.getElem?_eq_getElem indexBound, indexed], length⟩)
    simp [cap]
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.tail.data.val.length := by
      have := certificate.dataCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.tail.data.val[index]
    have found : inst.module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.datas index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    apply data_program_ready store inst code index segment block code.slot_count.val emitted sourceBound shape imports bindings
      (dataValid segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro length
    have cap := certificate.activeCapacity (Or.inr ⟨index, block, by rw [List.getElem?_eq_getElem indexBound, indexed], length⟩)
    simp [cap]
  · exact .done

/-- A nonreturning instruction cannot be the last instruction of a retained
initialization program. This supplies the decreasing finite-loop measure. -/
theorem SegmentCodeReady.next_bound {M : Type} {store : runtime.store.Store M}
    {inst code width position instruction} (ready : SegmentCodeReady store inst code width)
    (found : code.code.val[position]? = some instruction)
    (continues : segmentReturns instruction = false) : position + 1 < code.code.length := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have last := ready.returnLast
  rw [List.getLast?_eq_getElem?] at last
  by_contra failure
  have same : position = code.code.val.length - 1 := by simp only [alloc.vec.Vec.length] at *; omega
  rw [← same, found] at last
  have instructionEq := Option.some.inj last
  simp [instructionEq, segmentReturns] at continues

end Itasca.Store

end

/-! ## Segment Loop -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

def segmentRemaining (code : runtime.bytecode.CompiledFunction) (exec : runtime.interp.Execution)
    (status : core.result.Result Unit runtime.ExecError) : Nat :=
  match status, exec.frames.val with
  | .Ok _, [frame] => code.code.length - frame.pc.val + 1
  | _, _ => 0

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (position : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => SegmentAddressSpace store out.1 ∧ out.2.1 = platform ∧
        out.2.2.1.length = exec.slots.length ∧ SegmentStatus out.2.2.2 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨metadata, hostEq, slots, status, frameShape⟩
    dsimp only at metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      exact ⟨metadata, trivial, slots, status⟩
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        exact ⟨metadata, rfl, slots, status⟩
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        step with segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
          as ⟨result, next, after, host, effect⟩
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨.refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Itasca.Store

end

end

end

/-! ## SegmentSyntheticPreservation -/

section

/-!
Proofs for Runtime / Store / Initialization.

This module collects InitializerErrors, SegmentSyntheticPreservation.
Each section documents its contracts and consumers.
-/

/-! ## InitializerErrors -/

section

open Itasca.Representation

/-! ## SegmentInstructionShape -/

section

/-!
Store shape through segment initializer instructions. Bulk-operation shape preservation combines with ordinary instruction cases to retain the store invariant.
-/

/-! ## Segment Shape -/

section

namespace Itasca.Store
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

end Itasca.Store

end

/-! ## Segment Instruction Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

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

end Itasca.Store

end

end

/-! ## InitializerErrors -/

section

namespace Itasca.Store
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
        (∀ value, out.1 = .Ok value → Representation.rawType value = ty ∧
          Representation.sourceValue value = decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)) ∧
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

end Itasca.Store

end

end

/-! ## SegmentSyntheticPreservation -/

section

open Itasca.Representation

/-!
# Synthetic initializer preservation

Instruction metadata and synthetic-frame execution retain the source/store certificates needed to complete segment initialization.
-/

/-! ## SegmentInstructionMetadata -/

section SegmentInstructionMetadata

/-!
Segment initializer object-metadata preservation. Bulk-operation effects lift to every ready segment instruction while preserving object identities and maps.
-/

/-! ## Segment Bulk Metadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem segment_bulk_object_metadata {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ slots.length)
    (ready : SegmentBulkReady store inst code instruction) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => SegmentObjectMetadata view store out.2 ⦄ := by
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
    exact effect.object_metadata (List.getElem?_eq_getElem issuedMemory)
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
    exact effect.object_metadata (List.getElem?_eq_getElem issuedTable)
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop memory store instIndex function 0#usize slots inst data address found mapped issued)
    rintro out rfl
    exact .data_drop view store address _ (List.getElem?_eq_getElem issued)
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop memory store instIndex function 0#usize slots inst element address found mapped issued)
    rintro out rfl
    exact .element_drop view store address _ (List.getElem?_eq_getElem issued)

end Itasca.Store

end

/-! ## Segment Instruction Metadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

theorem segment_instruction_object_metadata {M P F A : Type}
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
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => SegmentObjectMetadata view store out.2.2.1 ⦄ := by
  cases ready with
  | constant dst bits bound =>
    apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
      inst code dst bits found functionFound frames fetched pcBound bound)
    rintro out ⟨success, next, nextValue, effect, rfl, rfl⟩
    exact .refl _ _
  | global index addr value mapped issued capacity =>
    apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
      inst code _ [value.lo] found functionFound (.global index addr value mapped issued)
      (by simpa using capacity) frames fetched pcBound)
    rintro out ⟨success, slots, next, nextValue, frames, rfl, rfl⟩
    exact .refl _ _
  | bulk instruction ready capacity =>
    apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position
      inst code instruction ready.kind found functionFound frames fetched pcBound _
      (segment_bulk_object_metadata memory view laws store instIndex function (alloc.vec.Vec.deref exec.slots)
        inst code instruction found functionFound (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using capacity)
        ready))
    rintro out ⟨next, nextValue, effect, rfl, metadata⟩
    exact metadata
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success, slots, empty, rfl, rfl⟩
    exact .refl _ _

end Itasca.Store

end

end SegmentInstructionMetadata

/-! ## SegmentSyntheticPreservation -/

section SegmentSyntheticPreservation

/-! ## SegmentLoopPreservation -/

section

/-!
Object metadata and shape preservation through the segment initialization loop. Totality and source correspondence remain separate to keep lightweight loop consumers independent of source simulation.
-/

/-! ## Segment Loop Metadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (position : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => SegmentObjectMetadata view store out.1 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => SegmentObjectMetadata view store state.1 ∧ SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨objects, metadata, hostEq, slots, status, frameShape⟩
    dsimp only at objects metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      simpa only [WP.spec_ok] using objects
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        simpa only [WP.spec_ok] using objects
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have typed := segment_instruction_object_metadata memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        step with segment_specs_and safe typed as ⟨result, next, after, host, effect, newObjects⟩
        have nextObjects := objects.trans newObjects
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata nextObjects
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextObjects, nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextObjects, nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨.refl _ _, .refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Itasca.Store

end

/-! ## Segment Loop Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (position : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length)
    (shape : Shape view store)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => Shape view out.1 ∧ SegmentTypes store out.1 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => Shape view state.1 ∧ SegmentTypes store state.1 ∧ SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨currentShape, types, metadata, hostEq, slots, status, frameShape⟩
    dsimp only at currentShape types metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      exact ⟨currentShape, types⟩
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        exact ⟨currentShape, types⟩
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have typed := segment_instruction_shape memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
          ((compatible instruction (List.mem_of_getElem? fetched)).transport types) currentShape
        step with segment_specs_and safe typed as ⟨result, next, after, host, effect, nextShape, newTypes⟩
        have nextTypes := types.trans newTypes
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata nextShape nextTypes
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextShape, nextTypes, nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextShape, nextTypes, nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨shape, .refl store, .refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Itasca.Store

end

end

/-! ## SegmentSyntheticPreservation -/

section

/-!
Synthetic initializer execution preserves object metadata and store shape. The totality and source-resource paths remain independent consumers of the lower loop.
-/

/-! ## Segment Synthetic Metadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- The actual synthetic entry point allocates its private slots/frame, then
runs the checked finite segment program. Allocation refusal and ordinary range
traps return normally; platform and address-space metadata are preserved. -/
theorem segment_synthetic_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => SegmentObjectMetadata view store out.2.1 ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact .refl _ _
  | Ok unitValue =>
    cases unitValue
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate code.slot_count.val 0#u64 := by
      simpa [alloc.vec.Vec.new] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact .refl _ _
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have nonempty : 0 < code.code.length := by
        have := ready.returnLast
        by_contra empty
        have nil : code.code.val = [] := List.eq_nil_of_length_eq_zero (by simp only [alloc.vec.Vec.length] at empty; omega)
        simp [nil] at this
      have capacity : prepared.slots.length = code.slot_count.val := by simp [alloc.vec.Vec.length, slots]
      have total := segment_loop_total memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      have typed := segment_loop_object_metadata memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, objects⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact objects
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact objects

end Itasca.Store

end

/-! ## Segment Synthetic Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- The actual synthetic entry point allocates its private slots/frame, then
runs the checked finite segment program. Allocation refusal and ordinary range
traps return normally; platform and address-space metadata are preserved. -/
theorem segment_synthetic_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (shape : Shape view store)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => Shape view out.2.1 ∧ SegmentTypes store out.2.1 ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨shape, .refl store⟩
  | Ok unitValue =>
    cases unitValue
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate code.slot_count.val 0#u64 := by
      simpa [alloc.vec.Vec.new] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact ⟨shape, .refl store⟩
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have nonempty : 0 < code.code.length := by
        have := ready.returnLast
        by_contra empty
        have nil : code.code.val = [] := List.eq_nil_of_length_eq_zero (by simp only [alloc.vec.Vec.length] at empty; omega)
        simp [nil] at this
      have capacity : prepared.slots.length = code.slot_count.val := by simp [alloc.vec.Vec.length, slots]
      have total := segment_loop_total memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      have typed := segment_loop_shape memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready) shape compatible
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, afterShape, types⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨afterShape, types⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact ⟨afterShape, types⟩

end Itasca.Store

end

end

end SegmentSyntheticPreservation

end

end
