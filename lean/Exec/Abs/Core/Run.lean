import Exec.Abs.Core.Correct
import Exec.Abs.Core.StatePreservation
import Exec.Abs.Core.Extension
import Exec.Abs.Core.Terminal

namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Finite successful transitions of the executable mutable machine. A host
boundary is handled separately and is not silently treated as a pure step. -/
inductive Run : Nat → AState → AState → Prop where
  | refl (s : AState) : Run 0 s s
  | next {s middle last : AState} {n : Nat} :
      step s = .next middle → Run n middle last → Run (n+1) s last

/-- A finite actual abstract run preserves the complete invariant, extends its
source store, and decodes to a counted specification reduction sequence. -/
theorem Run.correct {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : CoreState s) :
    CoreTyped last ∧ CoreState last ∧ Extend_store s.store last.store ∧
      ∃ count, StepsHN count (decode s) [] (decode last) := by
  induction run with
  | refl state => exact ⟨typed,covered,extend_store_refl _ typed.typed.store,0,.refl typed.typed.decode_wf⟩
  | @next state middle last n equation run ih =>
    obtain ⟨middleTyped,simulation⟩ := step_correct state middle typed covered equation
    have middleCore := step_core state middle typed.typed covered equation
    have extension := step_extends state middle typed covered equation
    obtain ⟨lastTyped,lastCore,lastExtension,count,tail⟩ := ih middleTyped middleCore
    refine ⟨lastTyped,lastCore,extend_store_trans extension lastExtension,?_⟩
    rcases simulation with ⟨same,_⟩ | ⟨first,_,head⟩
    · exact ⟨count,same.symm ▸ tail⟩
    · exact ⟨first+count,by simpa only [List.nil_append] using head.trans tail⟩

theorem Run.trap {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : CoreState s) (trapped : step last = .trap) :
    ∃ count, 0 < count ∧ StepsHN count (decode s) [] ⟨⟨last.store,last.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨lastTyped,lastCore,_,before,source⟩ := run.correct typed covered
  obtain ⟨after,positive,trap⟩ := step_trap last lastTyped lastCore trapped
  exact ⟨before+after,by omega,by simpa only [List.nil_append] using source.trans trap⟩

theorem Run.done {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : CoreState s) (values : List val)
    (done : step last = .done values) :
    ∃ count, StepsHN count (decode s) [] ⟨⟨last.store,last.ambient⟩,vals values⟩ := by
  obtain ⟨_,_,_,count,source⟩ := run.correct typed covered
  exact ⟨count,done_simulation last values done ▸ source⟩

end Exec.Abs.Core
