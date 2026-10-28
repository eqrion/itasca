import Exec.Abs.Core.Extension
import Exec.Abs.Supported.CoreStuck
namespace Itasca.Runtime.Abs.Supported
open Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

/-- The mutable machine preserves issued source objects by the generated store
extension relation at every successful transition. -/

theorem step_extends (s next : AState) (typed : CoreTyped s) (covered : SupportedState s)
    (equation : step s = .next next) : Extend_store s.store next.store := by
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
        · exact Core.instruction_extends source ambient frame rest op after next head typed equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation
      | nil =>
        have same := astep_store (s := ⟨source,ambient,frame :: rest,[]⟩) equation
        rw [same]
        exact extend_store_refl _ typed.typed.store

end Itasca.Runtime.Abs.Supported
