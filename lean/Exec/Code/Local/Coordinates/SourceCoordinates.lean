import Exec.Code.Local.Lowering.Common.Emit

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Retained source coordinates lie in the declared body interval, are ordered,
and do not exceed the compiler's current source cursor. -/
def SourceCoordinates {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  (∀ coordinate ∈ compiler.function.source_offsets.val.map UScalar.val,
    compiler.function.body_start.val ≤ coordinate ∧ coordinate < compiler.function.body_end.val ∧
      coordinate ≤ compiler.function.body_start.val+compiler.next_source.val) ∧
    (compiler.function.source_offsets.val.map UScalar.val).Pairwise (· ≤ ·)

theorem SourceCoordinates.bounds {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) :
    ∀ coordinate ∈ compiler.function.source_offsets.val.map UScalar.val,
      compiler.function.body_start.val ≤ coordinate ∧ coordinate < compiler.function.body_end.val ∧
        coordinate ≤ compiler.function.body_start.val+compiler.next_source.val := held.1

theorem SourceCoordinates.ordered {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) :
    (compiler.function.source_offsets.val.map UScalar.val).Pairwise (· ≤ ·) := held.2

theorem SourceCoordinates.empty {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (empty : compiler.function.source_offsets.val = []) : SourceCoordinates compiler := by
  constructor <;> simp [empty]

/-- Helpers that retain the coordinate vector and body interval preserve the
invariant whenever the source cursor moves forward. -/
theorem SourceCoordinates.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates before)
    (sources : after.function.source_offsets = before.function.source_offsets)
    (start : after.function.body_start = before.function.body_start)
    (finish : after.function.body_end = before.function.body_end)
    (cursor : before.next_source.val ≤ after.next_source.val) : SourceCoordinates after := by
  constructor
  · intro coordinate member
    rw [sources] at member
    obtain ⟨lower,upper,prior⟩ := held.bounds coordinate member
    rw [start,finish]
    exact ⟨lower,upper,by omega⟩
  · simpa only [sources] using held.ordered

/-- Actual emission appends precisely the current body-relative source origin.
The retained upper bound supplies ordering with every earlier instruction. -/
theorem Emitted.sourceCoordinates {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    SourceCoordinates after := by
  obtain ⟨budget,code,sources,frame,_,appended⟩ := emitted
  subst after
  constructor
  · intro coordinate member
    change coordinate ∈ sources.val.map UScalar.val at member
    change before.function.body_start.val ≤ coordinate ∧ coordinate < before.function.body_end.val ∧
      coordinate ≤ before.function.body_start.val+before.next_source.val
    rw [appended] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with prior | rfl
    · exact held.bounds coordinate prior
    · exact ⟨by omega,inside,Nat.le_refl _⟩
  · change (sources.val.map UScalar.val).Pairwise (· ≤ ·)
    rw [appended,List.pairwise_append]
    refine ⟨held.ordered,by simp,?_⟩
    intro earlier member later last
    simp only [List.mem_singleton] at last
    subst later
    exact (held.bounds earlier member).2.2

/-- Indexed form consumed by the real publication check, including the
previous-coordinate comparison at every nonzero instruction index. -/
theorem SourceCoordinates.checker {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) (index : Nat) (bound : index < compiler.function.source_offsets.length) :
    compiler.function.body_start.val ≤ compiler.function.source_offsets.val[index].val ∧
    compiler.function.source_offsets.val[index].val < compiler.function.body_end.val ∧
    (0 < index →
      (compiler.function.source_offsets.val[index-1]'(by
        have bounded : index < compiler.function.source_offsets.val.length := bound
        omega)).val ≤ compiler.function.source_offsets.val[index].val) := by
  have bounded : index < compiler.function.source_offsets.val.length := bound
  have member : compiler.function.source_offsets.val[index].val ∈
      compiler.function.source_offsets.val.map UScalar.val :=
    List.mem_map.mpr ⟨_,List.getElem_mem bounded,rfl⟩
  obtain ⟨lower,upper,_⟩ := held.bounds _ member
  refine ⟨lower,upper,?_⟩
  intro positive
  have order := List.pairwise_iff_getElem.mp held.ordered
  have previousBound : index-1 < (compiler.function.source_offsets.val.map UScalar.val).length := by
    simp only [List.length_map]
    omega
  have currentBound : index < (compiler.function.source_offsets.val.map UScalar.val).length := by
    simpa only [List.length_map] using bounded
  simpa only [List.getElem_map] using order (index-1) index previousBound currentBound (by omega)

end Itasca.Runtime.Code
