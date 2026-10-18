import Exec.Abs.Executable.Step
import Exec.Abs.Cumulative.Run
import Exec.Abs.Core.Run
namespace Exec.Abs.Executable
open SpecExt Exec.Spec Exec.Abs.Ownership

/-- A finite execution retains the actual permitted float and growth choices. -/
inductive Run : Nat → AState → AState → Prop where
  | refl (s : AState) : Run 0 s s
  | next {s middle last : AState} {n : Nat} :
      Step s (.next middle) → Run n middle last → Run (n+1) s last

theorem Run.correct {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : ExecutableState s) :
    CoreTyped last ∧ ExecutableState last ∧ Extend_store s.store last.store ∧
      ∃ count, StepsHN count (decode s) [] (decode last) := by
  induction run with
  | refl state => exact ⟨typed,covered,extend_store_refl _ typed.typed.store,0,.refl typed.typed.decode_wf⟩
  | @next state middle last n step run ih =>
    have middleTyped := step.next_typed typed covered
    have middleCovered := step.next_covered typed covered
    have extension := step.next_extends typed covered
    obtain ⟨lastTyped,lastCovered,lastExtension,count,tail⟩ := ih middleTyped middleCovered
    refine ⟨lastTyped,lastCovered,extend_store_trans extension lastExtension,?_⟩
    rcases step.next_simulation typed covered with ⟨same,_⟩ | ⟨first,_,head⟩
    · exact ⟨count,same.symm ▸ tail⟩
    · exact ⟨first+count,by simpa only [List.nil_append] using head.trans tail⟩

theorem Run.owned {bounds n s last} (run : Run n s last) (typed : CoreTyped s)
    (covered : ExecutableState s) (owned : StatefulOwned bounds s) : StatefulOwned bounds last := by
  induction run with
  | refl => exact owned
  | next step tail ih => exact ih (step.next_typed typed covered) (step.next_covered typed covered) (step.next_owned typed covered owned)

theorem Run.bound {bound n s last} (run : Run n s last) (typed : CoreTyped s)
    (covered : ExecutableState s) (bounded : CodeBound bound s) : CodeBound bound last := by
  induction run with
  | refl => exact bounded
  | next step tail ih => exact ih (step.next_typed typed covered) (step.next_covered typed covered) (step.next_bound typed covered bounded)

theorem Run.ambient {n s last} (run : Run n s last) : last.ambient = s.ambient := by
  induction run with
  | refl => rfl
  | next step tail ih => exact ih.trans step.next_ambient

theorem Run.trap {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : ExecutableState s) (trapped : Step last .trap) :
    ∃ count,0<count ∧ StepsHN count (decode s) [] ⟨⟨last.store,last.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨lastTyped,lastCovered,_,before,source⟩ := run.correct typed covered
  obtain ⟨after,positive,trap⟩ := trapped.trap_simulation lastTyped lastCovered
  exact ⟨before+after,by omega,by simpa only [List.nil_append] using source.trans trap⟩

theorem Step.done_simulation {s values} (step : Step s (.done values)) (typed : CoreTyped s) :
    decode s = ⟨⟨s.store,s.ambient⟩,vals values⟩ := by
  cases step with
  | cumulative old => exact old.done_simulation typed
  | simd impossible => cases impossible with
    | memory signature transition => cases transition

theorem Run.done {n : Nat} {s last : AState} (run : Run n s last)
    (typed : CoreTyped s) (covered : ExecutableState s) (values : List val)
    (done : Step last (.done values)) :
    ∃ count, StepsHN count (decode s) [] ⟨⟨last.store,last.ambient⟩,vals values⟩ := by
  obtain ⟨lastTyped,_,_,count,source⟩ := run.correct typed covered
  exact ⟨count,done.done_simulation lastTyped ▸ source⟩
end Exec.Abs.Executable
