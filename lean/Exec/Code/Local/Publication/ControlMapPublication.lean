import Exec.Code.Local.Publication.ControlMapBounds

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
