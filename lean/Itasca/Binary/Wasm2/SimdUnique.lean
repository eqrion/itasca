import Itasca.Binary.Wasm2.Simd
import Itasca.Binary.PrefixUnique

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

open ModuleBinary

private theorem pure_lane_disjoint {n op lane} (hp : pureMeaning n = some op)
    (hl : laneMeaning n = some lane) : False := by
  rw [lane_pure_none hl] at hp
  contradiction

private theorem pure_memory_disjoint {n op mem} (hp : pureMeaning n = some op)
    (hm : memoryMeaning n = some mem) : False := by
  rw [memory_pure_none hm] at hp
  contradiction

private theorem lane_memory_disjoint {n lane mem} (hl : laneMeaning n = some lane)
    (hm : memoryMeaning n = some mem) : False := by
  rw [memory_lane_none hm] at hl
  contradiction

/-- SIMD immediates determine one instruction and exact consumed prefix without typing premises. -/
theorem Immediate.prefix_unique (subopcode : U32) : PrefixUnique (Immediate subopcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact False.elim (pure_lane_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (pure_memory_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (lane_memory_disjoint ‹_› ‹_›) }
  case pure.pure =>
    rename_i op hp op' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact ⟨rfl, rfl, heq⟩
  case lane.lane =>
    rename_i op lane hp op' lane' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i op arg align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, rfl⟩ := leb_prefix_unique ho ho' hrest
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have he : arg = arg' := by cases arg; cases arg'; simp_all
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case memory.memoryLane =>
    rename_i op arg align offset hc ha ho hp op' arg' lane align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc' hc)
  case memoryLane.memory =>
    rename_i op arg lane align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc hc')
  case memoryLane.memoryLane =>
    rename_i op arg lane align offset hc ha ho hp op' arg' lane' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, htail⟩ := leb_prefix_unique ho ho' (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl⟩ := List.cons.inj htail
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have he : arg = arg' := by cases arg; cases arg'; simp_all
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case constant.constant | shuffle.shuffle =>
    rename_i low high lower upper hlo hhi low' high' lower' upper' hlo' hhi'
    obtain ⟨hloeq, rfl, hrest⟩ := float_prefix_unique 8 hlo hlo' (by simpa [List.append_assoc] using heq)
    obtain ⟨hhieq, rfl, rfl⟩ := float_prefix_unique 8 hhi hhi' hrest
    obtain rfl := UScalar.eq_of_val_eq hloeq
    obtain rfl := UScalar.eq_of_val_eq hhieq
    exact ⟨rfl, rfl, rfl⟩

end Itasca.Wasm2.Simd
