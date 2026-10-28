import Exec.Code.Local.Relations.Common.FutureFrames
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Invert the compiler's physical push without losing the source label or
that frame's separate guard and branch resolution groups. -/
theorem FramePlans.pop {length locals frames frame labels groups}
    (plans : FramePlans length locals (frames ++ [frame]) labels groups) :
    ∃ label outer pending guardTarget,
      labels = label :: outer ∧ groups = frameGroups frame label guardTarget ++ pending ∧
      FramePlans length locals frames outer pending ∧
      FrameFuture length locals frame label guardTarget := by
  generalize shape : frames ++ [frame] = physical at plans
  cases plans with
  | nil => simp at shape
  | @push old labels groups prior current label guardTarget future =>
    have size : frames.length = old.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append, List.length_singleton] at lengths
      omega
    obtain ⟨sameFrames, sameFrame⟩ := List.append_inj shape size
    simp only [List.cons.injEq, and_true] at sameFrame
    subst old current
    exact ⟨label, labels, groups, guardTarget, rfl, rfl, prior, future⟩

end Itasca.Runtime.Code
