import Itasca.Runtime.Abs.Core.Terminal
import Itasca.Runtime.Abs.Supported.CoreStuck
namespace Itasca.Runtime.Abs.Supported
open Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

theorem step_trap (s : AState) (typed : CoreTyped s) (covered : SupportedState s)
    (equation : step s = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode s) [] ⟨⟨s.store,s.ambient⟩,[.TRAP]⟩ := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have body := (covered.active frame (by simp)).1
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | cons op after =>
        rcases BinaryInstr.core_head (body op (by simp)) with head | stuck
        · exact Core.instruction_trap source ambient frame rest op after head typed equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation
      | nil =>
        simp only [step,astep,returnFrame,advance] at equation
        repeat' first | contradiction | split at equation

end Itasca.Runtime.Abs.Supported
