import Itasca.Runtime.Compiler.Local.Publication.ControlMapBounds

/-!
Publication of control maps when entering and closing scopes, retaining source coordinates and target bounds.
-/

/-! ## Control Map Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Physical frame owners of still-open control maps, in nesting order. -/
def activeControlMaps (compiler : runtime.compiler.FunctionCompiler A) : List Nat :=
  compiler.frames.val.map (fun frame => frame.map.val)

/-- Every map has a bounded entry and source origin. Maps whose owning frame
has closed additionally have ordered, bounded exit coordinates. Open frame
indices remain distinct and in their original declaration order. -/
structure ControlMapPublication (compiler : runtime.compiler.FunctionCompiler A) : Prop where
  ordered : (activeControlMaps compiler).Pairwise (· < ·)
  owners : ∀ index ∈ activeControlMaps compiler, index < compiler.function.controls.length
  entries : ∀ (index : Nat) (entry : runtime.compiler.ControlMap), compiler.function.controls.val[index]? = some entry → OpenControlMapBounds compiler entry
  closed : ∀ (index : Nat) (entry : runtime.compiler.ControlMap), compiler.function.controls.val[index]? = some entry →
    index ∉ activeControlMaps compiler → ClosedControlMapBounds compiler.function entry

/-- Ordinary metadata and code growth retain all control-map publication
bounds when frame ownership is unchanged and the source cursor advances. -/
theorem ControlMapPublication.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (controls : after.function.controls = before.function.controls)
    (active : activeControlMaps after = activeControlMaps before)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  refine ⟨by simpa only [active] using held.ordered,?_,?_,?_⟩
  · simpa only [active,controls] using held.owners
  · intro index entry lookup
    rw [controls] at lookup
    obtain ⟨pc,lower,source⟩ := held.entries index entry lookup
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  · intro index entry lookup inactive
    rw [controls] at lookup
    rw [active] at inactive
    exact (held.closed index entry lookup inactive).grow code start finish

/-- Fresh function-start metadata establishes the control-map invariant before
any body instruction, independently of any completed compilation certificate. -/
theorem ControlMapPublication.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (entry : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame)
    (controls : compiler.function.controls.val = [entry]) (frames : compiler.frames.val = [frame])
    (owner : frame.map.val = 0) (pc : entry.start_pc.val = 0)
    (source : entry.source_start = compiler.function.body_start) : ControlMapPublication compiler := by
  have active : activeControlMaps compiler = [0] := by simp [activeControlMaps,frames,owner]
  refine ⟨by simp [active],?_,?_,?_⟩
  · intro index member
    simp only [active,List.mem_singleton] at member
    subst index
    change 0 < compiler.function.controls.val.length
    simp [controls]
  · intro index map lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    rw [controls,List.length_singleton] at bound
    have zero : index = 0 := by omega
    subst index
    simp only [controls,List.getElem?_cons_zero,Option.some.injEq] at lookup
    subst map
    exact ⟨by rw [pc]; omega,by rw [source],by rw [source]; omega⟩
  · intro index map lookup inactive
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    rw [controls,List.length_singleton] at bound
    have zero : index = 0 := by omega
    subst index
    simp [active] at inactive

end Itasca.Runtime.Code

end

/-! ## Control Map Publication Close -/

section

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

end

/-! ## Control Map Publication Enter -/

section

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

end
