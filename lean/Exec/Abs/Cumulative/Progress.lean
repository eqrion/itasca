import Exec.Abs.Cumulative.Step
import Exec.Abs.Core.Progress
import Exec.Abs.FloatCore.Progress
namespace Exec.Abs.Cumulative

theorem instruction_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CumulativeInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op::after}::rest,[]⟩) :
    ∃ result, Step ⟨s,ambient,{f with code := op::after}::rest,[]⟩ result := by
  have frameTyped : FrameTyped s {f with code := op::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | core allowed =>
    obtain ⟨result,step⟩ := FloatCore.instruction_progress s ambient f rest op after allowed typed
    exact ⟨result,Step.of_float step⟩
  | stateful op =>
    obtain ⟨result,transition,safe⟩ := Stateful.transition_progress op s ambient {f with code := op.source::after} rest after typed
    refine ⟨result,.stateful transition ?_⟩
    intro impossible
    subst result
    exact safe
  | indirect_call table type =>
    cases table with
    | mk_uN table =>
      cases type with
      | mk_uN type =>
        exact ⟨_,.indirect rfl (Indirect.progress s ambient f rest table type after typed)⟩
  | block bt body covered =>
    exact ⟨_,.core rfl (block_progress s ambient f rest after bt body frameTyped)⟩
  | loop bt body covered =>
    exact ⟨_,.core rfl (loop_progress s ambient f rest after bt body frameTyped)⟩
  | ifelse bt yes no yesCovered noCovered =>
    exact ⟨_,.core rfl (if_progress s ambient f rest after bt yes no frameTyped)⟩

/-- Every typed Cumulative source state has an executable transition or explicit
result/trap/host boundary. Float operations retain their full result relation. -/
theorem step_progress (state : AState) (typed : CoreTyped state) (covered : CumulativeState state) :
    ∃ result, Step state result := by
  rcases state with ⟨s,ambient,frames,results⟩
  cases frames with
  | nil => exact ⟨_,.core rfl (by simp [Core.step])⟩
  | cons f rest =>
    have empty := typed.typed.activeResults (by simp)
    change results = [] at empty
    subst results
    have frameTyped : FrameTyped s f [] := by
      cases typed.typed.frames with | cons head _ => exact head
    have body := (covered.active f (List.mem_cons_self ..)).1
    cases f with
    | mk address resultTypes locals module labels code values =>
      let f : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | nil => exact ⟨_,.core rfl (empty_progress s ambient f rest frameTyped)⟩
      | cons op after => exact instruction_progress s ambient f rest op after (body op (by simp)) typed
end Exec.Abs.Cumulative
