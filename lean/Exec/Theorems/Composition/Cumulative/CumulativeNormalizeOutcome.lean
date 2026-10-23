import Exec.Interp.Core.BoundClosure
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
import Exec.Abs.Ownership.Core
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Control.NormalizeCompose
import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Interp.Cumulative.Erased
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem CumulativeFailure.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (failure : CumulativeFailure allocator hooks exec store platform ⟨s, ambient, middle :: rest, []⟩ error) :
    CumulativeFailure allocator hooks exec store platform ⟨s, ambient, before :: rest, []⟩ error := by
  rcases failure with ⟨kind, n, positive, steps⟩ | interrupted | rejected
  · refine Or.inl ⟨kind, ?_⟩
    rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
    · exact ⟨n, positive, by simpa only [same] using steps⟩
    · rcases simulation with ⟨same, _⟩ | ⟨m, hm, reductions⟩
      · exact ⟨n, positive, by simpa only [same] using steps⟩
      · exact ⟨m + n, by omega, by simpa using reductions.trans steps⟩
  · exact Or.inr (Or.inl interrupted)
  · obtain ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, cause⟩ := rejected
    refine Or.inr (Or.inr ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, ?_⟩)
    have counted : ∃ n, Spec.StepsHN n (Abs.decode ⟨s, ambient, before :: rest, []⟩) []
        (Abs.decode ⟨s, ambient, middle :: rest, []⟩) := by
      rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
      · subst middle
        exact ⟨0, .refl typed.decode_wf⟩
      · rcases simulation with ⟨same, _⟩ | ⟨n, positive, reductions⟩
        · exact ⟨0, by rw [← same]; exact .refl typed.decode_wf⟩
        · exact ⟨n, reductions⟩
    obtain ⟨n, steps⟩ := counted
    rcases cause with direct | ⟨code,indirect⟩
    · exact Or.inl (direct.prepend steps rfl rfl)
    · exact Or.inr ⟨code,indirect.prepend steps rfl rfl⟩

end Exec.Theorems
