import Exec.Code.Local.Capacity.SlotAvailability
import Exec.Code.Local.Relations.Common.SegmentProgram

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem offset_vector_width {env expr}
    (typed : Itasca.ModuleConstants.Valid env expr .I32) :
    ∀ lo hi, expr = .V128 lo hi → Itasca.types.ValueType.I32 = .V128 := by
  intro lo hi same
  subst expr
  cases typed

/-- The exact source segment program passes every local instruction gate.
Slot capacity is needed only for active five-instruction blocks. -/
theorem ElementProgram.instruction_accepts {function index segment instructions}
    (program : ElementProgram function index segment instructions)
    (typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid env offset .I32)
    (capacity : instructions.length = 5 → function.slot_count = 3#u32)
    (instruction : runtime.bytecode.Instr) (present : instruction ∈ instructions) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases program with
  | passive => simp at present
  | declarative mode word encoded =>
    simp only [List.mem_singleton] at present
    subst instruction
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
  | active table offset mode word length entry encoded count descriptor constantInstruction constant =>
    have slots := capacity rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · exact initial_instruction_capacity_accepts function offset .I32 _ constant
        (by simp [initializerWidth,slots]) (offset_vector_width (typed table offset mode))
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_accepts function 1#u32 1#u32 (by simp [slots])
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_accepts function 2#u32 1#u32 (by simp [slots])
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      rw [slots_fit_accepts function 0#u32 3#u32 (by simp [slots]),bind_ok]
      have inside := (List.getElem?_eq_some_iff.mp descriptor).1
      simpa [lift] using inside
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]

/-- Data segment programs need the same three slots and no pair descriptor. -/
theorem DataProgram.instruction_accepts {function index segment instructions}
    (program : DataProgram function index segment instructions)
    (typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid env offset .I32)
    (capacity : instructions.length = 5 → function.slot_count = 3#u32)
    (instruction : runtime.bytecode.Instr) (present : instruction ∈ instructions) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases program with
  | passive => simp at present
  | active memory offset mode word length encoded count constantInstruction constant =>
    have slots := capacity rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · exact initial_instruction_capacity_accepts function offset .I32 _ constant
        (by simp [initializerWidth,slots]) (offset_vector_width (typed memory offset mode))
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_accepts function 1#u32 1#u32 (by simp [slots])
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_accepts function 2#u32 1#u32 (by simp [slots])
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_accepts function 0#u32 3#u32 (by simp [slots])
    · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]

/-- Every retained segment instruction satisfies its independent slot and
auxiliary descriptor gates. Source offset typing supplies the literal-width
condition; the generated checker is not assumed successful. -/
theorem SegmentProgram.instructions_accept {module function} (program : SegmentProgram module function)
    (elementsTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instruction : runtime.bytecode.Instr) (member : instruction ∈ function.code.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  obtain ⟨elements,datas,body⟩ := program
  rw [body.instructions] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · obtain ⟨block,inBlocks,inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < module.module.env.elements.val.length := by
      have length := body.elementCount
      change elements.length = module.module.env.elements.val.length at length
      omega
    let segment := module.module.env.elements.val[index]
    have found : module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual,read,emitted⟩ := body.elements index segment found
    have same : actual = block := by
      rw [List.getElem?_eq_getElem bound] at read
      exact (Option.some.inj read).symm.trans equal
    subst actual
    apply emitted.instruction_accepts (elementsTyped segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro five
    exact body.activeCapacity (.inl ⟨index,block,by rw [List.getElem?_eq_getElem bound,equal],five⟩)
  · obtain ⟨block,inBlocks,inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < module.module.tail.data.val.length := by
      have length := body.dataCount
      change datas.length = module.module.tail.data.val.length at length
      omega
    let segment := module.module.tail.data.val[index]
    have found : module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual,read,emitted⟩ := body.datas index segment found
    have same : actual = block := by
      rw [List.getElem?_eq_getElem bound] at read
      exact (Option.some.inj read).symm.trans equal
    subst actual
    apply emitted.instruction_accepts (datasTyped segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro five
    exact body.activeCapacity (.inr ⟨index,block,by rw [List.getElem?_eq_getElem bound,equal],five⟩)
  · simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
    exact slots_fit_accepts function 0#u32 0#u32 (by scalar_tac)

/-- The actual synthetic publication checker accepts the source-ordered segment
program from its emitted syntax and empty synthetic metadata. This internal
lemma does not supply a code certificate as a public compiler premise. -/
theorem segment_program_well_formed {module function} (program : SegmentProgram module function)
    (elementsTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (offsets : function.source_offsets.val = []) (jumps : function.jump_tables.val = [])
    (controls : function.controls.val = []) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  obtain ⟨elements,datas,body⟩ := program
  have nonempty : 0 < function.code.length := by
    simp [alloc.vec.Vec.length,body.instructions]
  have lastReturn : function.code.val.getLast? = some (.Return 0#u32 0#u32) := by
    rw [body.instructions]
    simp
  apply well_formed_synthetic_accepts function start finish nonempty offsets
    (by rw [body.localSlots]; scalar_tac) (by rw [body.paramSlots,body.localSlots]) 0#u32 0#u32
  · simpa only [List.getLast?_eq_getElem?,alloc.vec.Vec.length] using lastReturn
  · intro index bound
    exact (show SegmentProgram module function from ⟨elements,datas,body⟩).instructions_accept
      elementsTyped datasTyped _ (List.getElem_mem bound)
  · simp [jumps]
  · simp [controls]

end Itasca.Runtime.Code
