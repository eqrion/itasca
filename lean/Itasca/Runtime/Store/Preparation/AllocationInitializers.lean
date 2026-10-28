import Itasca.Runtime.Store.Preparation.AllocationShape
import Itasca.Runtime.Store.Initialization.ElementContentEffect
import Itasca.Runtime.Store.Initialization.DataEffects

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : GlobalStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended globals addresses global appended mapped canonical room =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · intro value member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [GlobalShape, ReferenceShape] using shape.globals value old
      · simpa only [GlobalShape, ReferenceShape] using canonical
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
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem ElementContentEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst source status} (effect : ElementContentEffect store index inst source status after)
    (shape : AllocationShape view store) : AllocationShape view after := by
  cases effect with
  | failed error => exact shape
  | appended elements addresses values appended mapped canonical =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · intro element member word contained
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [ReferenceShape] using shape.elements element old word contained
      · simpa only [ReferenceShape] using canonical word contained
    · exact shape.canonicalTypes
    · exact shape.objectLimit
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem DataStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended datas addresses data appended mapped =>
    cases shape
    constructor <;> assumption

end Itasca.Runtime.Store
