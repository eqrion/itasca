import Exec.Abs.Core.Correct
import Exec.Abs.FloatCore.Dispatch
import Exec.Abs.FloatCoreState
namespace Exec.Abs.FloatCore
open Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : FloatCoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ next := by
  cases covered with
  | core allowed => exact Core.instruction_correct s ambient f rest op after next allowed typed equation
  | scalar op => rw [scalar_not_core] at equation; contradiction
  | block bt body _ =>
    have pure : astep ⟨s,ambient,{f with code := .BLOCK bt body :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨block_preservation s ambient f rest after bt body next typed.typed pure,?_⟩,
      typed_block_simulation s ambient f rest after bt body next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents
  | loop bt body _ =>
    have pure : astep ⟨s,ambient,{f with code := .LOOP bt body :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨loop_preservation s ambient f rest after bt body next typed.typed pure,?_⟩,
      typed_loop_simulation s ambient f rest after bt body next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents
  | ifelse bt yes no _ _ =>
    have pure : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩ = .next next := equation
    refine ⟨⟨core_if_preservation s ambient f rest bt yes no after next typed.typed pure,?_⟩,
      core_if_simulation s ambient f rest bt yes no after next typed.typed pure⟩
    simpa only [astep_store pure] using typed.contents


/-- Every successful mutable Core step is source typed and source simulated;
ordinary and mutable instructions share the same active/suspended-frame model. -/
theorem step_correct (s next : AState) (typed : CoreTyped s) (covered : FloatCoreState s)
    (equation : step s = .next next) : CoreTyped next ∧ NextSim s next := by
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
      | nil => exact empty_correct source ambient frame rest next typed equation
      | cons op after =>
        exact instruction_correct source ambient frame rest op after next (body op (by simp)) typed equation

end Exec.Abs.FloatCore
