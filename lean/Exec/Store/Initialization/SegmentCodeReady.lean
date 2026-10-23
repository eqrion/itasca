import Exec.Store.Initialization.SegmentCertificate

namespace Exec.Store
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
    (program : Code.SegmentProgram inst.module code)
    (pcBound : code.code.length < U32.max)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (elementsValid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (dataValid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.ModuleData.Valid inst.module.module.env segment) :
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

end Exec.Store
