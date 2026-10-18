import Exec.Abs.Ownership.Core
import Exec.Abs.Core.Run
namespace Exec.Abs.Ownership

theorem run_owned {bounds : Bounds} {n : Nat} {s last : AState}
    (run : Core.Run n s last) (typed : CoreTyped s) (covered : CoreState s)
    (owned : CoreOwned bounds s) : CoreOwned bounds last := by
  induction run with
  | refl => exact owned
  | next step rest ih =>
    exact ih (Core.step_correct _ _ typed covered step).1
      (Core.step_core _ _ typed.typed covered step) (step_owned typed covered owned step)

theorem done_values_owned {bounds : Bounds} {s : AState} {values : List val}
    (owned : CoreOwned bounds s) (done : Core.step s = .done values) : ValuesOwned bounds values := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => cases done; exact owned.values.1
  | cons frame rest =>
    cases frame with
    | mk address resultTypes locals module labels code operands =>
      cases code with
      | cons op after =>
        exact False.elim (Core.instruction_not_done store ambient
          ⟨address,resultTypes,locals,module,labels,op :: after,operands⟩ rest op after values done)
      | nil =>
        simp only [Core.step,astep,returnFrame,advance] at done
        repeat' first | contradiction | split at done
end Exec.Abs.Ownership
