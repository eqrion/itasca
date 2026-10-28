import Exec.Store.Preparation.AllocationShape

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : TableStageEffect store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, fit, room, counted, limited, rfl⟩
  · exact shape
  · have canonical : TableShape store {elements, ty := ty.elem, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp [zeros]
        scalar_tac
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have bound := fit.2
        simp only [maximumEq] at bound
        simpa [zeros] using bound.1
      · intro word member
        simp only [zeros, List.mem_replicate] at member
        rw [member.2]
        exact Or.inl rfl
    constructor
    · exact shape.identity
    · exact shape.memories
    · intro table member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [TableShape, ReferenceShape] using shape.tables table old
      · simpa only [TableShape, ReferenceShape] using canonical
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
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
    · simp [appended, zeros, counted, shape.tableAccounting]
    · exact limited

theorem MemoryStageEffect.allocated {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst ty out} (effect : MemoryStageEffect view store inst ty out) (shape : AllocationShape view store) :
    AllocationShape view out.2.1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, fit, room, counted, limited, rfl⟩
  · exact shape
  · have size : (view buffer).length = ty.limits.min.val * 65536 := by simpa using congrArg List.length zeros
    have canonical : MemoryShape view {buf := buffer, maximum := ty.limits.max} := by
      refine ⟨?_, ?_, ?_⟩
      · simp [size]
      · simpa [size] using fit.1
      · intro maximum maximumEq
        change ty.limits.max = some maximum at maximumEq
        have bound := fit.2
        simp only [maximumEq] at bound
        simpa [size] using bound
    constructor
    · exact shape.identity
    · intro memory member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact shape.memories memory old
      · exact canonical
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · simpa only [ReferenceShape] using shape.elements
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · simp [appended, counted, shape.memoryAccounting]
    · exact limited
    · exact shape.tableAccounting
    · exact shape.tableLimit

end Itasca.Runtime.Store
