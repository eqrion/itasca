import Exec.Code.Local.Publication.ControlMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Appending a fresh map and its uniquely indexed owner preserves every
closed range and the nesting order of all still-open map indices. -/
theorem ControlMapPublication.push {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (entry : runtime.compiler.ControlMap)
    (controls : after.function.controls.val = before.function.controls.val ++ [entry])
    (active : activeControlMaps after = activeControlMaps before ++ [before.function.controls.length])
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val)
    (fresh : OpenControlMapBounds after entry) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have length : after.function.controls.val.length = before.function.controls.val.length+1 := by
    simp [controls]
  have preserve (map : runtime.compiler.ControlMap) (bounds : OpenControlMapBounds before map) :
      OpenControlMapBounds after map := by
    obtain ⟨pc,lower,source⟩ := bounds
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [active,List.pairwise_append]
    refine ⟨held.ordered,by simp,?_⟩
    intro index member next singleton
    simp only [List.mem_singleton] at singleton
    subst next
    exact held.owners index member
  · intro index member
    rw [active] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · have oldBound := held.owners index old
      change index < after.function.controls.val.length
      change index < before.function.controls.val.length at oldBound
      omega
    · change before.function.controls.val.length < after.function.controls.val.length
      omega
  · intro index map lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    by_cases old : index < before.function.controls.val.length
    · rw [controls,List.getElem?_append_left old] at lookup
      exact preserve map (held.entries index map lookup)
    · have same : index = before.function.controls.val.length := by omega
      subst index
      simp [controls,List.getElem?_append] at lookup
      subst map
      exact fresh
  · intro index map lookup inactive
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have old : index < before.function.controls.val.length := by
      have different : index ≠ before.function.controls.val.length := by
        intro same
        apply inactive
        rw [active]
        apply List.mem_append_right
        simpa only [same,alloc.vec.Vec.length] using (List.mem_singleton_self before.function.controls.val.length)
      omega
    rw [controls,List.getElem?_append_left old] at lookup
    have oldInactive : index ∉ activeControlMaps before := by
      intro member
      apply inactive
      rw [active]
      exact List.mem_append_left _ member
    exact (held.closed index map lookup oldInactive).grow code start finish

end Itasca.Runtime.Code
