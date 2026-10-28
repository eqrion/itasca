import Exec.Store.Initialization.SegmentCompatible
import Exec.Store.Initialization.SegmentCertificate

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem constant_compatible {M : Type} {store : runtime.store.Store M} {inst code dst expr ty instruction}
    (constant : Code.ConstantInstruction code dst expr ty instruction) :
    SegmentBulkCompatible store inst code instruction := by
  cases constant <;> trivial

private theorem element_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.module.Element) (instructions : List runtime.bytecode.Instr)
    (program : Code.ElementProgram code index segment instructions)
    (found : inst.module.module.env.elements.val[index]? = some segment)
    (typed : Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : SegmentTypeBindings store inst) :
    ∀ instruction ∈ instructions, SegmentBulkCompatible store inst code instruction := by
  cases program with
  | passive mode => simp
  | declarative mode word encoded => simp [SegmentBulkCompatible]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    obtain ⟨tableBound, sameType, valid⟩ :=
      (show ∃ h : table.val < inst.module.module.env.table_types.val.length,
        inst.module.module.env.table_types.val[table.val].elem = segment.elem ∧
        Itasca.ModuleConstants.Valid inst.module.module.env offset .I32 from by simpa [mode] using typed.1)
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact constant_compatible constant
    · trivial
    · trivial
    · exact segment_table_compatible store inst code entry word table segment
        inst.module.module.env.table_types.val[table.val] descriptor (by simpa [encoded] using found)
        (List.getElem?_eq_getElem tableBound) sameType.symm bindings
    · trivial

private theorem data_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.module.Data) (instructions : List runtime.bytecode.Instr)
    (program : Code.DataProgram code index segment instructions) :
    ∀ instruction ∈ instructions, SegmentBulkCompatible store inst code instruction := by
  cases program with
  | passive mode => simp
  | active memory offset mode word length encoded count instruction constant =>
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact constant_compatible constant
    all_goals trivial

/-- The compiler's source-ordered program and staged type maps discharge all
reference-type compatibility requirements of its table initialization steps. -/
theorem segment_program_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (program : Code.SegmentProgram inst.module code) (bindings : SegmentTypeBindings store inst)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment) :
    ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction := by
  obtain ⟨elements, datas, certificate⟩ := program
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
    exact element_compatible store inst code index segment block emitted found
      (valid segment (List.mem_of_getElem? found)) bindings instruction inBlock
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
    exact data_compatible store inst code index segment block emitted instruction inBlock
  · trivial

end Itasca.Runtime.Store
