import Exec.Code.Local.Relations.Common.SegmentElement
import Exec.Code.Local.Initializer.InitializerElementLoop

namespace Itasca.Runtime.Code
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
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
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
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
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

end Itasca.Runtime.Code
