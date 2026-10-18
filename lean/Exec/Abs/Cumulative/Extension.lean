import Exec.Abs.Core.Extension
import Exec.Abs.Cumulative.Dispatch
import Exec.Abs.FloatCore.Extension
import Exec.Abs.CumulativeState
namespace Exec.Abs.Cumulative
open Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_extends (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CumulativeInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : Extend_store s next.store := by
  have unchanged (same : next.store = s) : Extend_store s next.store := by
    rw [same]
    exact extend_store_refl s typed.typed.store
  cases covered with
  | core allowed => exact FloatCore.instruction_extends s ambient f rest op after next allowed typed equation
  | stateful op => rw [stateful_not_core] at equation; contradiction
  | indirect_call table type => rw [indirect_not_core] at equation; contradiction
  | block bt body _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .BLOCK bt body :: after} :: rest,[]⟩) equation)
  | loop bt body _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .LOOP bt body :: after} :: rest,[]⟩) equation)
  | ifelse bt yes no _ _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩) equation)

/-- The mutable machine preserves issued source objects by the generated store
extension relation at every successful transition. -/

theorem step_extends (s next : AState) (typed : CoreTyped s) (covered : CumulativeState s)
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
      | cons op after => exact instruction_extends source ambient frame rest op after next (body op (by simp)) typed equation
      | nil =>
        have same := astep_store (s := ⟨source,ambient,frame :: rest,[]⟩) equation
        rw [same]
        exact extend_store_refl _ typed.typed.store

end Exec.Abs.Cumulative
