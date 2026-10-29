import Itasca.Runtime.Compiler.Local.Relations.Prefix.FutureFrames

/-!
A future plan after recording a forward branch yields the corresponding plan before it. The selected physical frame, source label, and one resolution group stay aligned, including guards belonging to intervening IF frames.

Main declarations: `FramePlans.before_mark`. A direct consumer is `Compiler.Body.Control.Control.CumulativePointControl`.
-/

namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A future plan after recording a forward branch yields the corresponding
plan before it. The selected physical frame, source label, and one resolution
group stay aligned, including guards belonging to intervening IF frames. -/
theorem FramePlans.before_mark {length locals updated labels groups}
    (plans : FramePlans length locals updated labels groups)
    {original : List runtime.compiler.Frame} {index depth : Nat} {frame : runtime.compiler.Frame}
    (fixups : alloc.vec.Vec Usize)
    (replacement : updated = original.set index {frame with end_reachable := true, fixups})
    (found : original[index]? = some frame)
    (position : index + depth + 1 = original.length) :
    ∃ label before after, labels[depth]? = some label ∧ label.branchLive = true ∧
      FramePlans length locals original labels (before ++ ⟨frame.fixups.val, label.target⟩ :: after) ∧
      groups = before ++ ⟨fixups.val, label.target⟩ :: after := by
  induction plans generalizing original index depth with
  | nil =>
    have size := congrArg List.length replacement
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.length_nil, List.length_set] at size
    omega
  | @push frames labels groups prior top label guardTarget future ih =>
    rcases List.eq_nil_or_concat original with empty | ⟨initial, last, originalEq⟩
    · simp [empty] at found
    · rw [List.concat_eq_append] at originalEq
      subst original
      have lengths : frames.length = initial.length := by
        have size := congrArg List.length replacement
        simp only [List.length_set, List.length_append, List.length_singleton] at size
        omega
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at bound position
      by_cases atTop : index = initial.length
      · have sameFrame : last = frame := by simpa [atTop] using found
        subst last
        have zero : depth = 0 := by omega
        have replaced : frames ++ [top] = initial ++ [{frame with end_reachable := true, fixups}] := by
          simpa [atTop, List.set_append_right, Nat.le_refl] using replacement
        obtain ⟨sameInitial, sameTop⟩ := List.append_inj replaced lengths
        simp only [List.cons.injEq, and_true] at sameTop
        subst initial top
        refine ⟨label, (match frame.if_pc with | none => [] | some site => [⟨[site], guardTarget⟩]), groups,
          by simp [zero], future.marked rfl, ?_, ?_⟩
        · have planned := FramePlans.push prior frame label guardTarget
            (FrameFuture.previous_mark (frame := frame) (fixups := fixups) future)
          convert planned using 1 <;> simp [frameGroups, List.append_assoc] <;> rfl
        · simp [frameGroups, List.append_assoc]
          <;> rfl
      · have inside : index < initial.length := by omega
        have positive : 0 < depth := by omega
        have replaced : frames ++ [top] =
            initial.set index {frame with end_reachable := true, fixups} ++ [last] := by
          simpa only [List.set_append_left index _ inside] using replacement
        obtain ⟨sameInitial, sameTop⟩ := List.append_inj replaced (by simpa using lengths)
        simp only [List.cons.injEq, and_true] at sameTop
        subst top
        obtain ⟨chosen, before, after, labelAt, live, previous, grouped⟩ := ih sameInitial
          (by simpa only [List.getElem?_append_left inside] using found)
          (depth := depth - 1) (by omega)
        refine ⟨chosen, frameGroups last label guardTarget ++ before, after, ?_, live, ?_, ?_⟩
        · have decomp : depth = (depth - 1) + 1 := by omega
          rw [decomp, List.getElem?_cons_succ]
          exact labelAt
        · simpa only [List.append_assoc] using FramePlans.push previous last label guardTarget future
        · simp only [grouped, List.append_assoc]

end Itasca.Runtime.Code
