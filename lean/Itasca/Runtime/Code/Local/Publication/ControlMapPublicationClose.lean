import Itasca.Runtime.Code.Local.Publication.ControlMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Popping the innermost owner and recording its bounded exit preserves all
other control-map ranges. The source origin remains the one established at entry. -/
theorem ControlMapPublication.close {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (index : Nat) (entry closed : runtime.compiler.ControlMap) (remaining : List Nat)
    (found : before.function.controls.val[index]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set index closed)
    (owners : activeControlMaps before = remaining ++ [index])
    (active : activeControlMaps after = remaining)
    (source : closed.source_start = entry.source_start)
    (bounded : ClosedControlMapBounds before.function closed)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have indexBound := (List.getElem?_eq_some_iff.mp found).1
  have length : after.function.controls.val.length = before.function.controls.val.length := by simp [controls]
  have preserve (map : runtime.compiler.ControlMap) (bounds : OpenControlMapBounds before map) :
      OpenControlMapBounds after map := by
    obtain ⟨pc,lower,prior⟩ := bounds
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  have newBounds : OpenControlMapBounds after closed := by
    obtain ⟨ordered,pc,lower,upper,positive⟩ := bounded
    obtain ⟨_,_,origin⟩ := held.entries index entry found
    refine ⟨(ordered.trans pc).trans code,by simpa only [start] using lower,?_⟩
    rw [start,source]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have ordered := held.ordered
    rw [owners,List.pairwise_append] at ordered
    simpa only [active] using ordered.1
  · intro owner member
    rw [active] at member
    have prior := held.owners owner (by rw [owners]; exact List.mem_append_left _ member)
    change owner < after.function.controls.val.length
    change owner < before.function.controls.val.length at prior
    omega
  · intro other map lookup
    by_cases same : index = other
    · subst other
      rw [controls,List.getElem?_set_self indexBound] at lookup
      have equal := Option.some.inj lookup
      subst map
      exact newBounds
    · rw [controls,List.getElem?_set_ne same] at lookup
      exact preserve map (held.entries other map lookup)
  · intro other map lookup inactive
    by_cases same : index = other
    · subst other
      rw [controls,List.getElem?_set_self indexBound] at lookup
      have equal := Option.some.inj lookup
      subst map
      exact bounded.grow code start finish
    · rw [controls,List.getElem?_set_ne same] at lookup
      have priorInactive : other ∉ activeControlMaps before := by
        intro member
        rw [owners] at member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with old | equal
        · apply inactive
          simpa only [active] using old
        · exact same equal.symm
      exact (held.closed other map lookup priorInactive).grow code start finish

/-- After the last owner closes, the actual root-return emission makes every
control-map target strictly smaller than the completed code length. -/
theorem ControlMapPublication.close_last_publish {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (index : Nat) (entry closed : runtime.compiler.ControlMap)
    (found : before.function.controls.val[index]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set index closed)
    (owners : activeControlMaps before = [index])
    (bounded : ClosedControlMapBounds before.function closed)
    (code : before.function.code.length < after.function.code.length) :
    ∀ map ∈ after.function.controls.val,
      map.start_pc.val ≤ map.end_pc.val ∧ map.end_pc.val < after.function.code.length ∧
      after.function.body_start.val ≤ map.source_start.val ∧ map.source_end.val ≤ after.function.body_end.val ∧
      map.source_start.val < map.source_end.val := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have indexBound := (List.getElem?_eq_some_iff.mp found).1
  intro map member
  obtain ⟨other,lookup⟩ := List.mem_iff_getElem?.mp member
  by_cases same : index = other
  · subst other
    rw [controls,List.getElem?_set_self indexBound] at lookup
    have equal := Option.some.inj lookup
    subst map
    exact bounded.publish code start finish
  · rw [controls,List.getElem?_set_ne same] at lookup
    have inactive : other ∉ activeControlMaps before := by simpa only [owners,List.mem_singleton] using Ne.symm same
    exact (held.closed other map lookup inactive).publish code start finish

end Itasca.Runtime.Code
