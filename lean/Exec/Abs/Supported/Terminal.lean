import Exec.Abs.Cumulative.Terminal
import Exec.Abs.Supported.Language
namespace Exec.Abs.Supported
open Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_trap (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  cases covered with
  | cumulative allowed => exact Cumulative.instruction_trap s ambient f rest op after allowed typed equation
  | external impossible => rw [impossible] at equation; contradiction
  | block bt body =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | loop bt body =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | ifelse bt yes no =>
    simp only [instruction,astep,advance] at equation
    repeat' first | contradiction | split at equation


theorem step_trap (s : AState) (typed : CoreTyped s) (covered : SupportedState allowed s)
    (heads : ∀ {op}, allowed op → CoreHead op)
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
      | cons op after => exact instruction_trap source ambient frame rest op after (heads (body op (by simp))) typed equation
      | nil =>
        simp only [step,astep,returnFrame,advance] at equation
        repeat' first | contradiction | split at equation

end Exec.Abs.Supported
