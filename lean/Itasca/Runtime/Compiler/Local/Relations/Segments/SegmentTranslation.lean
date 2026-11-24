import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Local.Initializer.ModuleMappings
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Module.Elab.SegmentTyping
import Itasca.Runtime.Compiler.Local.Source.ModuleSourceAndSubmission

/-!
Proofs for Runtime / Compiler / Local / Relations / Segments.

This module collects SegmentTranslation, SegmentFlowSource.
Each section documents its contracts and consumers.
-/

/-! ## SegmentTranslation -/

section

open Itasca.Representation

/-!
# Segment Translation

Element and data segment prefixes compose into complete initializer programs. Acceptance, loop and finish relations retain source order and exact emitted instructions.
-/

/-! ## SegmentAcceptance -/

section

/-!
The exact source segment program passes every local instruction gate. Slot capacity is needed only for active five-instruction blocks.

Main declarations: `ElementProgram.instruction_accepts` and `segment_program_well_formed`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem offset_vector_width {env expr}
    (typed : Itasca.Module.Constants.Valid env expr .I32) :
    ∀ lo hi, expr = .V128 lo hi → Itasca.wasm_types.ValueType.I32 = .V128 := by
  intro lo hi same
  subst expr
  cases typed

/-- The exact source segment program passes every local instruction gate.
Slot capacity is needed only for active five-instruction blocks. -/
theorem ElementProgram.instruction_accepts {function index segment instructions}
    (program : ElementProgram function index segment instructions)
    (typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid env offset .I32)
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
      Itasca.Module.Constants.Valid env offset .I32)
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
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
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
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
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

end Itasca.Compiler

end

/-! ## SegmentFinish -/

section

/-!
Element/data initializer program prefixes, loops and finishing. SegmentProgram.change_module transports the completed segment certificate to its final module context.
-/

/-! ## Segment Element -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem emit_element_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (valid : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, ElementProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count, indirect := after.indirect} ∧
      after.indirect.val.take before.indirect.length = before.indirect.val ∧
      (instructions.length ≤ 1 ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  exact runtime.compiler.initialize.emit_element.inv ops law module budget afterBudget before after index segment found valid success

end Itasca.Compiler

end

/-! ## Segment Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem ElementProgram.extend {before after : runtime.bytecode.CompiledFunction}
    {index segment instructions} (program : ElementProgram before index segment instructions)
    (pool : after.v128_pool = before.v128_pool)
    (indirect : after.indirect.val.take before.indirect.length = before.indirect.val) :
    ElementProgram after index segment instructions := by
  cases program with
  | passive mode => exact .passive mode
  | declarative mode word encoded => exact .declarative mode word encoded
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    refine .active table offset mode word length entry encoded count ?_ instruction (constant.change_code pool)
    have bound := (List.getElem?_eq_some_iff.mp descriptor).1
    have same := congrArg (fun values => values[entry.val]?) indirect
    simp only [List.getElem?_take, bound, if_pos] at same
    exact same.trans descriptor

theorem DataProgram.extend {before after : runtime.bytecode.CompiledFunction}
    {index segment instructions} (program : DataProgram before index segment instructions)
    (pool : after.v128_pool = before.v128_pool) : DataProgram after index segment instructions := by
  cases program with
  | passive mode => exact .passive mode
  | active memory offset mode word length encoded count instruction constant =>
    exact .active memory offset mode word length encoded count instruction (constant.change_code pool)

structure ElementProgramPrefix (module : runtime.compiler.ExecutableModule)
    (seed current : runtime.bytecode.CompiledFunction) (count : Nat)
    (programs : List (List runtime.bytecode.Instr)) : Prop where
  length : programs.length = count
  entries : ∀ index, index < count → ∃ segment instructions,
    module.module.env.elements.val[index]? = some segment ∧ programs[index]? = some instructions ∧
    ElementProgram current index segment instructions
  code : current.code.val = seed.code.val ++ programs.flatten
  fields : current = {seed with code := current.code, indirect := current.indirect, slot_count := current.slot_count}
  indirect : current.indirect.val.take seed.indirect.length = seed.indirect.val
  capacity : current.slot_count = seed.slot_count ∨ current.slot_count = 3#u32
  active : ∀ instructions ∈ programs, instructions.length = 5 → current.slot_count = 3#u32

theorem ElementProgramPrefix.empty (module : runtime.compiler.ExecutableModule)
    (seed : runtime.bytecode.CompiledFunction) : ElementProgramPrefix module seed seed 0 [] := by
  constructor <;> simp

theorem element_program_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction) (programs : List (List runtime.bytecode.Instr))
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementProgramPrefix module seed current index.val programs)
    (bound : index.val < module.module.env.elements.length)
    (valid : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget current index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ nextPrograms, ElementProgramPrefix module seed after (index.val + 1) nextPrograms := by
  let segment := module.module.env.elements.val[index.val]
  have found : module.module.env.elements.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  obtain ⟨instructions, program, code, fields, indirect, capacity⟩ :=
    emit_element_program ops law module budget afterBudget current after index segment found
      (valid segment (by simp [segment]) ) success
  have pool : after.v128_pool = current.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool fields
    exact same
  refine ⟨programs ++ [instructions], ?_⟩
  constructor
  · simp [prefixInv.length]
  · intro i hi
    by_cases old : i < index.val
    · obtain ⟨oldSegment, oldInstructions, oldFound, oldProgram, oldCertificate⟩ := prefixInv.entries i old
      refine ⟨oldSegment, oldInstructions, oldFound, ?_, oldCertificate.extend pool indirect⟩
      simpa [List.getElem?_append, prefixInv.length, old] using oldProgram
    · have last : i = index.val := by omega
      subst i
      exact ⟨segment, instructions, found, by simp [prefixInv.length], program⟩
  · simp [code, prefixInv.code, List.flatten_append, List.append_assoc]
  · rw [fields, prefixInv.fields]
  · exact initializer_prefix_trans prefixInv.indirect indirect
  · rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
    · simpa only [same] using prefixInv.capacity
    · exact .inr three
  · intro body member five
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · have oldActive := prefixInv.active body previous five
      rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
      · exact same.trans oldActive
      · exact three
    · rcases capacity with ⟨small, _⟩ | ⟨_, three⟩
      · omega
      · exact three

structure DataProgramPrefix (module : runtime.compiler.ExecutableModule)
    (seed current : runtime.bytecode.CompiledFunction) (count : Nat)
    (programs : List (List runtime.bytecode.Instr)) : Prop where
  length : programs.length = count
  entries : ∀ index, index < count → ∃ segment instructions,
    module.module.tail.data.val[index]? = some segment ∧ programs[index]? = some instructions ∧
    DataProgram current index segment instructions
  code : current.code.val = seed.code.val ++ programs.flatten
  fields : current = {seed with code := current.code, slot_count := current.slot_count}
  capacity : current.slot_count = seed.slot_count ∨ current.slot_count = 3#u32
  active : ∀ instructions ∈ programs, instructions.length = 5 → current.slot_count = 3#u32

theorem DataProgramPrefix.empty (module : runtime.compiler.ExecutableModule)
    (seed : runtime.bytecode.CompiledFunction) : DataProgramPrefix module seed seed 0 [] := by
  constructor <;> simp

theorem data_program_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction) (programs : List (List runtime.bytecode.Instr))
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataProgramPrefix module seed current index.val programs)
    (bound : index.val < module.module.tail.data.length)
    (valid : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget current index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ nextPrograms, DataProgramPrefix module seed after (index.val + 1) nextPrograms := by
  let segment := module.module.tail.data.val[index.val]
  have found : module.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  obtain ⟨instructions, program, code, fields, capacity⟩ :=
    emit_data_program ops law module budget afterBudget current after index segment found
      (valid segment (by simp [segment]) ) success
  have pool : after.v128_pool = current.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool fields
    exact same
  refine ⟨programs ++ [instructions], ?_⟩
  constructor
  · simp [prefixInv.length]
  · intro i hi
    by_cases old : i < index.val
    · obtain ⟨oldSegment, oldInstructions, oldFound, oldProgram, oldCertificate⟩ := prefixInv.entries i old
      refine ⟨oldSegment, oldInstructions, oldFound, ?_, oldCertificate.extend pool⟩
      simpa [List.getElem?_append, prefixInv.length, old] using oldProgram
    · have last : i = index.val := by omega
      subst i
      exact ⟨segment, instructions, found, by simp [prefixInv.length], program⟩
  · simp [code, prefixInv.code, List.flatten_append, List.append_assoc]
  · rw [fields, prefixInv.fields]
  · rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
    · simpa only [same] using prefixInv.capacity
    · exact .inr three
  · intro body member five
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · have oldActive := prefixInv.active body previous five
      rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
      · exact same.trans oldActive
      · exact three
    · rcases capacity with ⟨empty, _⟩ | ⟨_, three⟩
      · simp [empty] at five
      · exact three

end Itasca.Compiler

end

/-! ## Segment Loops -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem element_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : ElementProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.env.elements.length)
    (valid : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, ElementProgramPrefix module seed after module.module.env.elements.length finalPrograms := by
  let P := fun (_ : runtime.compiler.Budget A) current (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ module.module.env.elements.length ∧
      ∃ programs, ElementProgramPrefix module seed current cursor.val programs
  let Q := fun (_ : runtime.compiler.Budget A) current (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ∃ programs, ElementProgramPrefix module seed current module.module.env.elements.length programs
  have completed := InitializerSegmentLoop.inv
    { rules := initializerEmitElementLoop ops module, budget := budget, function := current, index := index, status := .Ok (),
      P := P, Q := Q,
      advance := (by
        intro charged current cursor inside prior result nextBudget nextFunction nextIndex called increment accepted
        subst result
        obtain ⟨position, programs, mapped⟩ := prior rfl
        change cursor.val < module.module.env.elements.length at inside
        obtain ⟨nextPrograms, appended⟩ := element_program_append ops law module seed current nextFunction
          programs charged nextBudget cursor mapped inside valid called
        exact ⟨by omega, nextPrograms, by simpa only [increment] using appended⟩),
      finish := (by
        intro charged current cursor result prior stopped accepted
        obtain ⟨position, programs, mapped⟩ := prior accepted
        have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
        change module.module.env.elements.length ≤ cursor.val at last
        have equal : cursor.val = module.module.env.elements.length := by omega
        exact ⟨programs, by simpa only [equal] using mapped⟩),
      initial := fun _ => ⟨bound, programs, prefixInv⟩ } budgetAfter after (.Ok ()) success
  exact completed rfl

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem data_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : DataProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.tail.data.length)
    (valid : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, DataProgramPrefix module seed after module.module.tail.data.length finalPrograms := by
  let P := fun (_ : runtime.compiler.Budget A) current (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ module.module.tail.data.length ∧
      ∃ programs, DataProgramPrefix module seed current cursor.val programs
  let Q := fun (_ : runtime.compiler.Budget A) current (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ∃ programs, DataProgramPrefix module seed current module.module.tail.data.length programs
  have completed := InitializerSegmentLoop.inv
    { rules := initializerEmitDataLoop ops module, budget := budget, function := current, index := index, status := .Ok (),
      P := P, Q := Q,
      advance := (by
        intro charged current cursor inside prior result nextBudget nextFunction nextIndex called increment accepted
        subst result
        obtain ⟨position, programs, mapped⟩ := prior rfl
        change cursor.val < module.module.tail.data.length at inside
        obtain ⟨nextPrograms, appended⟩ := data_program_append ops law module seed current nextFunction
          programs charged nextBudget cursor mapped inside valid called
        exact ⟨by omega, nextPrograms, by simpa only [increment] using appended⟩),
      finish := (by
        intro charged current cursor result prior stopped accepted
        obtain ⟨position, programs, mapped⟩ := prior accepted
        have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
        change module.module.tail.data.length ≤ cursor.val at last
        have equal : cursor.val = module.module.tail.data.length := by omega
        exact ⟨programs, by simpa only [equal] using mapped⟩),
      initial := fun _ => ⟨bound, programs, prefixInv⟩ } budgetAfter after (.Ok ()) success
  exact completed rfl

end Itasca.Compiler

end

/-! ## Segment Finish -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem segment_program_finish (module : runtime.compiler.ExecutableModule)
    (seed first second : runtime.bytecode.CompiledFunction)
    (instructions : alloc.vec.Vec runtime.bytecode.Instr)
    (elements datas : List (List runtime.bytecode.Instr))
    (elementPrefix : ElementProgramPrefix module seed first module.module.env.elements.length elements)
    (dataPrefix : DataProgramPrefix module first second module.module.tail.data.length datas)
    (appended : instructions.val = second.code.val ++ [.Return 0#u32 0#u32])
    (emptyCode : seed.code.val = []) (emptyLocals : seed.locals.val = [])
    (localSlots : seed.local_slots = 0#u32) (paramSlots : seed.param_slots = 0#u32)
    (capacity : seed.slot_count = 0#u32) :
    SegmentProgram module {second with code := instructions} := by
  have secondPool : second.v128_pool = first.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool dataPrefix.fields
    exact same
  have secondIndirect : second.indirect = first.indirect := by
    have same := congrArg runtime.bytecode.CompiledFunction.indirect dataPrefix.fields
    exact same
  have secondCapacity : second.slot_count = 0#u32 ∨ second.slot_count = 3#u32 := by
    rcases dataPrefix.capacity with same | three
    · rcases elementPrefix.capacity with original | three
      · exact .inl (same.trans (original.trans capacity))
      · exact .inr (same.trans three)
    · exact .inr three
  refine ⟨elements, datas, ?_⟩
  constructor
  · exact elementPrefix.length
  · exact dataPrefix.length
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := elementPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend secondPool (by simp only [secondIndirect, List.take_length])⟩
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := dataPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend rfl⟩
  · simp [appended, dataPrefix.code, elementPrefix.code, emptyCode, List.append_assoc]
  · exact secondCapacity
  · rintro (⟨index, body, found, five⟩ | ⟨index, body, found, five⟩)
    · have firstThree := elementPrefix.active body (List.mem_of_getElem? found) five
      rcases dataPrefix.capacity with same | three
      · exact same.trans firstThree
      · exact three
    · exact dataPrefix.active body (List.mem_of_getElem? found) five
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.local_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.local_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans localSlots)
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.param_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.param_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans paramSlots)
  · have secondFields := congrArg (fun f => f.locals.val) dataPrefix.fields
    have firstFields := congrArg (fun f => f.locals.val) elementPrefix.fields
    exact secondFields.trans (firstFields.trans emptyLocals)

theorem SegmentProgram.change_module {before after : runtime.compiler.ExecutableModule}
    {function} (program : SegmentProgram before function) (source : after.module = before.module) :
    SegmentProgram after function := by
  obtain ⟨elements, datas, certificate⟩ := program
  refine ⟨elements, datas, ?_⟩
  cases certificate
  constructor <;> (try simp only [source]) <;> assumption

end Itasca.Compiler

end

end

/-! ## SegmentComplete -/

section

/-!
Actual successful initializer lowering supplies both the read-only maps and the exact retained segment-writing program, from canonical source offset typing. The bytecode checker's successful Boolean is eliminated from the actual call.

Main declarations: `initializer_lower_segments`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual successful initializer lowering supplies both the read-only maps and
the exact retained segment-writing program, from canonical source offset typing.
The bytecode checker's successful Boolean is eliminated from the actual call. -/
theorem initializer_lower_segments {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A)
    (emptyGlobals : module.global_initializers.val = [])
    (emptyElements : module.element_initializers.val = [])
    (emptyElementOffsets : module.element_offsets.val = [])
    (emptyDataOffsets : module.data_offsets.val = [])
    (validElements : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (validDatas : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower ops module budget = .ok (.Ok (), after, budgetAfter)) :
    after.module = module.module ∧
      after.functions.val.take module.functions.length = module.functions.val ∧ InitializerMappings after ∧
      ∃ function, after.functions.val[after.initialization.val]? = some function ∧ SegmentProgram after function := by
  obtain ⟨stages, ⟨publication⟩⟩ := runtime.compiler.initialize.lower.success ops module after budget budgetAfter success
  have mapping := stages.mappings law emptyGlobals emptyElements emptyElementOffsets emptyDataOffsets
  rcases stages with ⟨globalsModule, elementsModule, dataModule, b1, b2, b3, globalsCall, elementsCall, dataCall⟩
  rcases publication with ⟨function, function1, function2, b4, b5, b6, code, functions,
    seed, emitElements, emitData, emitReturn, check, pushed, frame⟩
  obtain ⟨sourceAll, allPrefix, mapped⟩ := mapping
  change dataModule.module = module.module at sourceAll
  have seedEq : function = {initializerSeed .I32 with slot_count := 0#u32} := by
    change Result.ok {initializerSeed .I32 with slot_count := 0#u32} = Result.ok function at seed
    exact (Result.ok_injective seed).symm
  obtain ⟨elementPrograms, elementCertificate⟩ := element_program_loop ops law dataModule function function function1
    b3 b4 0#usize [] (.empty _ _) (by simp) (by simpa only [sourceAll] using validElements) emitElements
  obtain ⟨dataPrograms, dataCertificate⟩ := data_program_loop ops law dataModule function1 function1 function2
    b4 b5 0#usize [] (.empty _ _) (by simp) (by simpa only [sourceAll] using validDatas) emitData
  subst after
  obtain ⟨_, functionsEq⟩ := budget_push_success ops law b6 budgetAfter dataModule.functions functions
    { function2 with code := code } pushed
  have prefixFinal : functions.val.take dataModule.functions.length = dataModule.functions.val := by
    simp [functionsEq]
  refine ⟨sourceAll,

    initializer_prefix_trans allPrefix prefixFinal, ?_, ?_⟩
  · exact ⟨mapped.globals.extend prefixFinal, mapped.elementValues.extend prefixFinal,
      mapped.elementOffsets.extend prefixFinal, mapped.dataOffsets.extend prefixFinal⟩
  · refine ⟨{function2 with code := code}, ?_, ?_⟩
    · simp [functionsEq]
    · have appended := initializer_emit_success ops law b5 b6 function2.code code _ emitReturn
      have program := segment_program_finish dataModule function function1 function2 code
        elementPrograms dataPrograms elementCertificate dataCertificate appended
        (by simp [seedEq, initializerSeed]) (by simp [seedEq, initializerSeed])
        (by simp [seedEq, initializerSeed]) (by simp [seedEq, initializerSeed])
        (by simp [seedEq, initializerSeed])
      exact program.change_module rfl

end Itasca.Compiler

end

/-! ## SegmentTranslation -/

section

/-!
Source instructions represented by the straight-line segment bytecode.

Main declarations: `segmentInstructionSource` and `segmentSource`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std SpecExt

/-- Source instructions represented by the straight-line segment bytecode. -/
def segmentInstructionSource (code : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → List admininstr
  | .Const32 _ bits => [Spec.Segment.i32 bits.val]
  | .GlobalGet _ index => [.GLOBAL_GET (.mk_uN index.val)]
  | .MemoryInit _ index => [.MEMORY_INIT (.mk_uN index.val)]
  | .TableInit _ entry =>
      let pair := code.indirect.val[entry.val]!
      [.TABLE_INIT (.mk_uN pair.2.val) (.mk_uN pair.1.val)]
  | .DataDrop index => [.DATA_DROP (.mk_uN index.val)]
  | .ElemDrop index => [.ELEM_DROP (.mk_uN index.val)]
  | _ => []

def segmentSource (code : runtime.bytecode.CompiledFunction) (instructions : List runtime.bytecode.Instr) : List admininstr :=
  instructions.flatMap (segmentInstructionSource code)

/-- The pending operand count is a syntactic property of emitted segment groups. -/
inductive SegmentFlow : Nat → List runtime.bytecode.Instr → Prop where
  | done : SegmentFlow 0 [.Return 0#u32 0#u32]
  | constant (pending : Nat) (dst bits : U32) (rest : List runtime.bytecode.Instr)
      (slot : dst.val = pending) (bound : pending < 3) (next : SegmentFlow (pending+1) rest) :
      SegmentFlow pending (.Const32 dst bits :: rest)
  | global (index : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 1 rest) :
      SegmentFlow 0 (.GlobalGet 0#u32 index :: rest)
  | memory (data : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 3 (.MemoryInit 0#u32 data :: rest)
  | table (entry : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 3 (.TableInit 0#u32 entry :: rest)
  | dataDrop (data : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 0 (.DataDrop data :: rest)
  | elementDrop (element : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 0 (.ElemDrop element :: rest)

theorem segment_source_wf (code : runtime.bytecode.CompiledFunction) (instructions : List runtime.bytecode.Instr) :
    Forall wf_admininstr (segmentSource code instructions) := by
  intro instruction member
  obtain ⟨raw, _, member⟩ := List.mem_flatMap.mp member
  unfold segmentInstructionSource at member
  split at member <;> simp only [List.mem_singleton,List.not_mem_nil] at member
  all_goals subst instruction
  · exact Spec.Segment.i32_wf _ (by scalar_tac)
  · exact .admininstr_case_46 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_66 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_54 _ _ (Spec.Segment.index_wf _ (by scalar_tac)) (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_67 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_55 _ (Spec.Segment.index_wf _ (by scalar_tac))

end Itasca.Compiler

end

end

/-! ## SegmentFlowSource -/

section

open Itasca.Representation

/-!
Every emitted global read uses an imported i32 global.

Main declarations: `SegmentGlobalTypes`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem constant_i32_flow {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : Module.Constants.Valid env expr valueType)
    (typeEq : valueType = .I32)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 1 rest) :
    SegmentFlow 0 (instruction :: rest) := by
  cases valid with
  | i32 value =>
    cases constant
    exact .constant 0 _ _ rest rfl (by decide) next
  | globalGet index ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    exact .global index rest next
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

private theorem constant_i32_source {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : Module.Constants.Valid env expr valueType)
    (typeEq : valueType = .I32) :
    segmentInstructionSource function instruction =
      (Module.Constants.expression expr).map admininstr_instr := by
  cases valid with
  | i32 value =>
    cases constant
    simp [segmentInstructionSource, Spec.Segment.i32, Module.Constants.expression,
      Module.Constants.instruction, Itasca.Spec.i32Const, admininstr_instr, IScalar.hcast_val_eq]
  | globalGet index ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    rfl
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

theorem ElementProgram.flow {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : Module.Segments.elementValid env segment)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (instructions ++ rest) := by
  cases program with
  | passive mode => exact next
  | declarative mode word encoded => exact .elementDrop word rest next
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    apply constant_i32_flow constant offsetValid rfl
    exact .constant 1 1#u32 0#u32 _ rfl (by decide)
      (.constant 2 2#u32 length _ rfl (by decide) (.table entry _ (.elementDrop word rest next)))

theorem DataProgram.flow {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : Module.Data.Valid env segment)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (instructions ++ rest) := by
  cases program with
  | passive mode => exact next
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      unfold Module.Data.Valid at valid
      rw [mode] at valid
      exact valid.2
    apply constant_i32_flow constant offsetValid rfl
    exact .constant 1 1#u32 0#u32 _ rfl (by decide)
      (.constant 2 2#u32 length _ rfl (by decide) (.memory word _ (.dataDrop word rest next)))

private theorem flatten_flow (groups : List (List runtime.bytecode.Instr))
    (flows : ∀ group ∈ groups, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest))
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (groups.flatten ++ rest) := by
  induction groups with
  | nil => exact next
  | cons group groups ih =>
    have tailFlow := ih (fun item member => flows item (by simp [member]))
    simpa only [List.flatten_cons, List.append_assoc] using
      flows group (by simp) (groups.flatten ++ rest) tailFlow

theorem SegmentProgram.flow {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      Module.Segments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, Module.Data.Valid module.module.env segment) :
    SegmentFlow 0 function.code.val := by
  obtain ⟨elements, datas, body⟩ := program
  have elementFlows : ∀ group ∈ elements, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest) := by
    intro group member rest next
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.env.elements.val.length := by
      have length := body.elementCount
      change elements.length = module.module.env.elements.val.length at length
      omega
    let segment := module.module.env.elements.val[index]
    have found : module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual, actualFound, actualProgram⟩ := body.elements index segment found
    have same : actual = group := by
      rw [List.getElem?_eq_getElem bound] at actualFound
      exact (Option.some.inj actualFound).symm.trans equal
    subst actual
    exact actualProgram.flow (elementValid segment (List.mem_of_getElem? found)) rest next
  have dataFlows : ∀ group ∈ datas, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest) := by
    intro group member rest next
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.tail.data.val.length := by
      have length := body.dataCount
      change datas.length = module.module.tail.data.val.length at length
      omega
    let segment := module.module.tail.data.val[index]
    have found : module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual, actualFound, actualProgram⟩ := body.datas index segment found
    have same : actual = group := by
      rw [List.getElem?_eq_getElem bound] at actualFound
      exact (Option.some.inj actualFound).symm.trans equal
    subst actual
    exact actualProgram.flow (dataValid segment (List.mem_of_getElem? found)) rest next
  rw [body.instructions]
  simpa only [List.append_assoc] using flatten_flow elements elementFlows
    (datas.flatten ++ [.Return 0#u32 0#u32]) (flatten_flow datas dataFlows _ .done)

theorem ElementProgram.source {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : Module.Segments.elementValid env segment) :
    segmentSource function instructions =
      (Spec.Segment.elementProgram (Module.Elaboration.element (Module.Environment.rawElement segment)) (.mk_uN index)).map admininstr_instr := by
  cases program with
  | passive mode => simp [segmentSource, Spec.Segment.elementProgram, Module.Elaboration.element, Module.Environment.rawElement, Module.Segments.elementMode, mode]
  | declarative mode word encoded => simp [segmentSource, segmentInstructionSource, Spec.Segment.elementProgram, Module.Elaboration.element, Module.Environment.rawElement, Module.Segments.elementMode, mode, encoded, admininstr_instr]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    simp only [segmentSource, List.flatMap_cons, List.flatMap_nil, constant_i32_source constant offsetValid rfl]
    simp [segmentInstructionSource, Spec.Segment.elementProgram, Module.Elaboration.element, Module.Environment.rawElement,
      Module.Segments.elementMode, mode, encoded, count, admininstr_instr, List.getElem!_eq_getElem?_getD,
      descriptor, Spec.Segment.i32, List.append_assoc]

theorem DataProgram.source {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : Module.Data.Valid env segment) :
    segmentSource function instructions =
      (Spec.Segment.dataProgram (Module.Data.translate (Module.Data.raw segment)) (.mk_uN index)).map admininstr_instr := by
  cases program with
  | passive mode => simp [segmentSource, Spec.Segment.dataProgram, Module.Data.translate, Module.Data.raw, Module.Segments.dataMode, mode]
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      unfold Module.Data.Valid at valid
      rw [mode] at valid
      exact valid.2
    simp only [segmentSource, List.flatMap_cons, List.flatMap_nil, constant_i32_source constant offsetValid rfl]
    simp [segmentInstructionSource, Spec.Segment.dataProgram, Module.Data.translate, Module.Data.raw,
      Module.Segments.dataMode, mode, encoded, count, admininstr_instr, Spec.Segment.i32, List.append_assoc]

private theorem group_sources {T : Type} [Inhabited T]
    (function : runtime.bytecode.CompiledFunction) (groups : List (List runtime.bytecode.Instr))
    (sources : List T) (translate : T → Nat → List admininstr)
    (count : groups.length = sources.length)
    (entries : ∀ (index : Nat) source, sources[index]? = some source → ∃ group,
      groups[index]? = some group ∧ segmentSource function group = translate source index) :
    segmentSource function groups.flatten =
      ((List.range sources.length).map (fun index => translate sources[index]! index)).flatten := by
  have mapped : groups.map (segmentSource function) =
      (List.range sources.length).map (fun index => translate sources[index]! index) := by
    apply List.ext_getElem
    · simp [count]
    · intro index left right
      have sourceBound : index < sources.length := by simpa using right
      have groupBound : index < groups.length := by simpa using left
      obtain ⟨group, found, translated⟩ := entries index sources[index] (List.getElem?_eq_getElem sourceBound)
      have same : group = groups[index] := by
        rw [List.getElem?_eq_getElem groupBound] at found
        exact (Option.some.inj found).symm
      simpa only [List.getElem_map, List.getElem_range, getElem!_pos sources index sourceBound, same] using translated
  rw [← mapped]
  clear mapped entries count sources
  induction groups with
  | nil => rfl
  | cons group groups ih => simpa [segmentSource, List.flatMap_append] using congrArg (segmentSource function group ++ ·) ih

private theorem mapped_programs {T U : Type} [Inhabited T] [Inhabited U]
    (sources : List T) (translate : T → U) (program : U → idx → List instr) :
    (((List.range sources.length).map (fun index =>
      (program (translate sources[index]!) (.mk_uN index)).map admininstr_instr)).flatten) =
    (((List.range (sources.map translate).length).map (fun index =>
      program (sources.map translate)[index]! (.mk_uN index))).flatten).map admininstr_instr := by
  rw [List.map_flatten]
  congr 1
  simp only [List.map_map, List.length_map]
  apply List.map_congr_left
  intro index member
  have bound := List.mem_range.mp member
  have mappedBound : index < (sources.map translate).length := by simpa using bound
  simp only [Function.comp_def, getElem!_pos sources index bound,
    getElem!_pos (sources.map translate) index mappedBound, List.getElem_map]

/-- The complete emitted initializer represents the source-ordered generated
segment programs; the final synthetic Return has empty source code. -/
theorem SegmentProgram.source {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      Module.Segments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, Module.Data.Valid module.module.env segment) :
    segmentSource function function.code.val =
      (Spec.Segment.elementPrograms (module.module.env.elements.val.map (fun entry =>
        Module.Elaboration.element (Module.Environment.rawElement entry)))).flatten.map admininstr_instr ++
      (Spec.Segment.dataPrograms (module.module.tail.data.val.map (fun entry =>
        Module.Data.translate (Module.Data.raw entry)))).flatten.map admininstr_instr := by
  letI : Inhabited Itasca.metadata.Element := ⟨⟨.FuncRef, .Passive, default⟩⟩
  letI : Inhabited Itasca.metadata.Data := ⟨⟨.Passive, default⟩⟩
  obtain ⟨elements, datas, body⟩ := program
  have elementSources := group_sources function elements module.module.env.elements.val
    (fun entry index => (Spec.Segment.elementProgram (Module.Elaboration.element (Module.Environment.rawElement entry))
      (.mk_uN index)).map admininstr_instr) body.elementCount (by
        intro index segment found
        obtain ⟨group, located, represented⟩ := body.elements index segment found
        exact ⟨group, located, represented.source (elementValid segment (List.mem_of_getElem? found))⟩)
  have dataSources := group_sources function datas module.module.tail.data.val
    (fun entry index => (Spec.Segment.dataProgram (Module.Data.translate (Module.Data.raw entry))
      (.mk_uN index)).map admininstr_instr) body.dataCount (by
        intro index segment found
        obtain ⟨group, located, represented⟩ := body.datas index segment found
        exact ⟨group, located, represented.source (dataValid segment (List.mem_of_getElem? found))⟩)
  have elementMapped := mapped_programs module.module.env.elements.val (fun entry => Module.Elaboration.element (Module.Environment.rawElement entry)) Spec.Segment.elementProgram
  rw [elementMapped] at elementSources
  have dataMapped := mapped_programs module.module.tail.data.val (fun entry => Module.Data.translate (Module.Data.raw entry)) Spec.Segment.dataProgram
  rw [dataMapped] at dataSources
  rw [body.instructions]
  simp only [segmentSource, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    segmentInstructionSource, List.append_nil]
  exact congrArg₂ (· ++ ·) elementSources dataSources

/-- Every emitted global read uses an imported i32 global. -/
def SegmentGlobalTypes (env : Itasca.metadata.Env) (instructions : List runtime.bytecode.Instr) : Prop :=
  ∀ slot index, runtime.bytecode.Instr.GlobalGet slot index ∈ instructions →
    ∃ ty, env.global_types.val[index.val]? = some ty ∧ ty.valtype = .I32 ∧
      index.val < env.num_imported_globals.val

private theorem constant_i32_global_type {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : Module.Constants.Valid env expr valueType) (typeEq : valueType = .I32) :
    SegmentGlobalTypes env [instruction] := by
  intro slot index member
  have equal := List.mem_singleton.mp member
  cases valid with
  | i32 value => cases constant; cases equal
  | globalGet idx ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    cases equal
    exact ⟨ty, by simpa [typed] using List.getElem?_eq_getElem bound, typeEq, imported⟩
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

theorem ElementProgram.global_types {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : Module.Segments.elementValid env segment) : SegmentGlobalTypes env instructions := by
  cases program with
  | passive mode => simp [SegmentGlobalTypes]
  | declarative mode word encoded => simp [SegmentGlobalTypes]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    intro slot index member
    have justConstant : runtime.bytecode.Instr.GlobalGet slot index ∈ [instruction] := by simpa using member
    exact constant_i32_global_type constant offsetValid rfl slot index justConstant

theorem DataProgram.global_types {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : Module.Data.Valid env segment) : SegmentGlobalTypes env instructions := by
  cases program with
  | passive mode => simp [SegmentGlobalTypes]
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : Module.Constants.Valid env offset .I32 := by
      unfold Module.Data.Valid at valid
      rw [mode] at valid
      exact valid.2
    intro slot index member
    have justConstant : runtime.bytecode.Instr.GlobalGet slot index ∈ [instruction] := by simpa using member
    exact constant_i32_global_type constant offsetValid rfl slot index justConstant

private theorem groups_property {T : Type} (groups : List (List runtime.bytecode.Instr))
    (sources : List T) (env : Itasca.metadata.Env) (count : groups.length = sources.length)
    (entries : ∀ (index : Nat) source, sources[index]? = some source → ∃ group,
      groups[index]? = some group ∧ SegmentGlobalTypes env group) :
    SegmentGlobalTypes env groups.flatten := by
  intro slot index member
  obtain ⟨group, present, instruction⟩ := List.mem_flatten.mp member
  obtain ⟨ordinal, bound, equal⟩ := List.mem_iff_getElem.mp present
  have sourceBound : ordinal < sources.length := by omega
  obtain ⟨actual, found, types⟩ := entries ordinal sources[ordinal] (List.getElem?_eq_getElem sourceBound)
  have same : actual = group := by
    rw [List.getElem?_eq_getElem bound] at found
    exact (Option.some.inj found).symm.trans equal
  subst actual
  exact types slot index instruction

theorem SegmentProgram.global_types {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      Module.Segments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, Module.Data.Valid module.module.env segment) :
    SegmentGlobalTypes module.module.env function.code.val := by
  obtain ⟨elements, datas, body⟩ := program
  have elementTypes := groups_property elements module.module.env.elements.val module.module.env
    body.elementCount (by
      intro index segment found
      obtain ⟨group, located, represented⟩ := body.elements index segment found
      exact ⟨group, located, represented.global_types (elementValid segment (List.mem_of_getElem? found))⟩)
  have dataTypes := groups_property datas module.module.tail.data.val module.module.env
    body.dataCount (by
      intro index segment found
      obtain ⟨group, located, represented⟩ := body.datas index segment found
      exact ⟨group, located, represented.global_types (dataValid segment (List.mem_of_getElem? found))⟩)
  intro slot index member
  rw [body.instructions] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | impossible
  · exact elementTypes slot index member
  · exact dataTypes slot index member
  · cases impossible

end Itasca.Compiler

end
