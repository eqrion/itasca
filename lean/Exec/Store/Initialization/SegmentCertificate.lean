import Exec.Store.Initialization.SegmentInstruction
import Exec.Store.Initialization.InitializerCertificates
import Exec.Code.Local.Relations.Common.SegmentData
import Exec.Code.Local.Capacity.SegmentBound

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem offset_instruction_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (instruction : runtime.bytecode.Instr) (width : Nat)
    (typed : Itasca.ModuleConstants.Valid inst.module.module.env expr .I32)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (emitted : Code.ConstantInstruction code 0#u32 expr .I32 instruction)
    (capacity : 1 ≤ width) : SegmentInstructionReady store inst code width instruction := by
  obtain ⟨words, resolved⟩ := initializer_resolves store inst expr .I32 typed bindings imports
  rcases Code.valid_offset_shape typed with ⟨bits, rfl⟩ | ⟨index, rfl⟩
  · cases emitted
    exact .constant _ _ (by simp; omega)
  · cases emitted
    cases resolved with
    | global ty index addr value mapped found typed scalar =>
      exact .global index addr value mapped found capacity

/-- A retained element block uses only indices already issued by staging. -/
theorem element_program_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.module.Element) (instructions : List runtime.bytecode.Instr)
    (width : Nat) (program : Code.ElementProgram code index segment instructions)
    (sourceBound : index < inst.module.module.env.elements.length)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (typed : Itasca.ModuleSegments.elementValid inst.module.module.env segment)
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
        Itasca.ModuleConstants.Valid inst.module.module.env offset .I32 from by simpa [mode] using typed.1)
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
    (index : Nat) (segment : Itasca.module.Data) (instructions : List runtime.bytecode.Instr)
    (width : Nat) (program : Code.DataProgram code index segment instructions)
    (sourceBound : index < inst.module.module.tail.data.length)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (typed : Itasca.ModuleData.Valid inst.module.module.env segment)
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
        Itasca.ModuleConstants.Valid inst.module.module.env offset .I32 from by simpa [Itasca.ModuleData.Valid, mode] using typed)
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

end Itasca.Runtime.Store
