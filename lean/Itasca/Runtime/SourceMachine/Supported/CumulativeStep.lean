import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.SourceMachine.Core.Extension
import Itasca.Runtime.SourceMachine.Indirect.Transport
import Itasca.Runtime.SourceMachine.SupportedState
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Core.Terminal
import Itasca.Runtime.SourceMachine.Cumulative.Step

/-!
Supported source execution: correctness, ownership, code bounds, extension and terminal cases compose the cumulative step theorem. The independently consumed coverage contract remains separate.
-/

/-! ## Bound -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Core

theorem step_bound (bound : Nat) (s next : AState)
    (typed : CoreTyped s) (covered : SupportedState s) (bounded : CodeBound bound s)
    (step : Core.step s = .next next) : CodeBound bound next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have empty := typed.typed.activeResults (by simp)
    change results = [] at empty
    subst results
    have supported := (covered.active frame (by simp)).1
    have frameTyped : FrameTyped store frame [] := by cases typed.typed.frames with | cons head _ => exact head
    have hbounded := bounded.frames frame (by simp)
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | cons op after =>
        rcases BinaryInstr.core_head (supported op (by simp)) with head | stuck
        · exact Core.instruction_bound bound store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next head frameTyped bounded step
        · exact nomatch (stuck _ _ _ _ _).symm.trans step
      | nil =>
        cases labels with
        | nil => exact return_frame_bound bounded step
        | cons label labels =>
          simp only [Core.step,astep] at step
          split at step
          · apply advance_bound bounded step
            refine ⟨?_,fun l member => hbounded.2 l (by simp [member])⟩
            have hh := hbounded.2 label (by simp)
            have hp := list_size_append label.cont label.after
            have hpos : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
            change sizeOf label.after ≤ bound
            omega
          · contradiction
end Itasca.Runtime.SourceMachine.Supported

end

/-! ## Correct -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

/-- Every successful mutable Core step is source typed and source simulated;
ordinary and mutable instructions share the same active/suspended-frame model. -/
theorem step_correct (s next : AState) (typed : CoreTyped s) (covered : SupportedState s)
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
        rcases BinaryInstr.core_head (body op (by simp)) with head | stuck
        · exact Core.instruction_correct source ambient frame rest op after next head typed equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation

end Itasca.Runtime.SourceMachine.Supported

end

/-! ## Extension -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Core
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

end Itasca.Runtime.SourceMachine.Supported

end

/-! ## Indirect -/

section

namespace Itasca.Runtime.SourceMachine.Indirect

theorem invoke_supported {s : AState} {f : AFrame} {rest : List AFrame} {address after next}
    (functions : FunctionsSupported s.store) (tail : Forall BinaryInstr after)
    (labels : Forall (fun label => Forall BinaryInstr label.cont ∧ Forall BinaryInstr label.after) f.labels)
    (frames : Forall (FrameSupported) rest)
    (stepped : invoke s f rest address after=.next next) : SupportedState next := by
  cases lookup : s.store.FUNCS[address]? with
  | none => simp [invoke,lookup] at stepped
  | some fn =>
    have function := functions fn (List.mem_of_getElem? lookup)
    cases signature : fn.TYPE with
    | mk_functype params results =>
      cases params with
      | mk_list params =>
        cases results with
        | mk_list results =>
          cases body : fn.CODE with
          | HOST host =>
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
          | FUNC index locals source =>
            simp only [body] at function
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
            cases stepped
            refine ⟨?_,functions⟩
            intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨function,by simp [Forall]⟩
            · rcases List.mem_cons.mp member with rfl | member
              · exact ⟨tail,labels⟩
              · exact frames frame member

theorem step_supported {s ambient f rest table type after next}
    (covered : SupportedState ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : SupportedState next := by
  have frame := covered.active {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_supported (f:={f with vals:=_}) covered.functions (fun item member => frame.1 item (List.mem_cons_of_mem _ member)) frame.2
    (fun item member => covered.active item (List.mem_cons_of_mem _ member)) stepped


end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Ownership -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Ownership

theorem step_owned {bounds : Bounds} {s next : AState}
    (typed : CoreTyped s) (covered : SupportedState s) (owned : CoreOwned bounds s)
    (step : Core.step s = .next next) : CoreOwned bounds next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have first := owned.values.2 frame (by simp)
    have remaining : ∀ item ∈ rest, FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
    have supported := (covered.active frame (by simp)).1
    have frameTyped : FrameTyped store frame [] := by cases typed.typed.frames with | cons head _ => exact head
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | nil =>
        have pureStep : astep ⟨store,ambient,⟨address,types,locals,module,labels,[],values⟩ :: rest,results⟩ = .next next := step
        refine ⟨?_,by rw [astep_store pureStep]; exact owned.globals⟩
        cases labels with
        | nil => exact ownership_return first remaining owned.values.1 pureStep
        | cons label labels =>
          simp only [astep] at pureStep
          split at pureStep
          · apply ownership_advance (step := pureStep) owned.values.1
            · exact first
            · exact remaining
          · contradiction
      | cons op after =>
        rcases BinaryInstr.core_head (supported op (by simp)) with head | stuck
        · exact Ownership.instruction_owned bounds store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next head frameTyped owned.globals first remaining step
        · exact nomatch (stuck _ _ _ _ _).symm.trans step
end Itasca.Runtime.SourceMachine.Supported

end

/-! ## State Preservation -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Core

/-- Successful instructions retain the supported source grammar, including
unchanged defined function bodies after mutable object-content writes. -/
theorem instruction_covered (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : CoreHead op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall BinaryInstr after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure typed] at equation
    exact slice_instruction_covered s ambient f rest _ after next pure covered equation
  | const ty value => exact advance_covered covered equation ⟨tail,labels⟩
  | select =>
    simp only [instruction,select] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | global_get index =>
    cases index
    simp only [instruction,globalGet] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | global_set index =>
    cases index
    simp only [instruction,globalSet] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_covered ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩
  | load descriptor argument =>
    rw [instruction_load] at equation
    simp only [load] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | store descriptor argument =>
    rw [instruction_store] at equation
    simp only [Core.store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_covered ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩

/-- The source grammar and retained function-body coverage survive every
successful Core transition; no immutable-store assumption is used. -/
theorem step_covered (s next : AState) (typed : ATyped s) (covered : SupportedState s)
    (equation : step s = .next next) : SupportedState next := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have frameTyped : FrameTyped source frame [] := by
      cases typed.frames with | cons head _ => exact head
    have body := covered.active frame (by simp)
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | cons op after =>
        rcases SourceMachine.BinaryInstr.core_head (body.1 op (by simp)) with head | stuck
        · exact instruction_covered source ambient frame rest op after next head frameTyped covered equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation
      | nil =>
        cases labels with
        | nil => exact return_frame_covered covered equation
        | cons label labels =>
          simp only [step,astep] at equation
          split at equation
          · apply advance_covered covered equation
            exact ⟨(body.2 label (by simp)).2,fun outer member => body.2 outer (by simp [member])⟩
          · contradiction

end Itasca.Runtime.SourceMachine.Supported

end

/-! ## Terminal -/

section

namespace Itasca.Runtime.SourceMachine.Supported
open Itasca.Runtime.SourceMachine.Core
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

end Itasca.Runtime.SourceMachine.Supported

end

/-! ## Cumulative Step -/

section

namespace Itasca.Runtime.SourceMachine.Cumulative
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

theorem Step.next_typed_supported {before next : AState} (step : Step before (.next next))
 (typed : CoreTyped before) (covered : SupportedState before) : CoreTyped next := by
  cases step with
  | core equation executable => exact (Supported.step_correct before next typed covered equation).1
  | scalar transition =>
    have fresh := Float.transition_preservation _ _ _ _ _ _ _ typed.typed transition
    cases transition
    exact ⟨fresh,typed.contents⟩

  | indirect equation _ => exact Indirect.preservation _ _ _ _ _ _ _ _ typed equation
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).1

theorem Step.next_covered_supported {before next : AState} (step : Step before (.next next))
 (typed : CoreTyped before) (covered : SupportedState before) : SupportedState next := by
  cases step with
  | core equation executable => exact Supported.step_covered before next typed.typed covered equation
  | scalar transition =>
    cases transition with
    | next front a b bits values first second effect =>
      apply Supported.advance_covered covered rfl
      have frame := covered.active _ (List.mem_cons_self ..)
      exact ⟨fun i member => frame.1 i (List.mem_cons_of_mem _ member),frame.2⟩

  | indirect equation _ => exact Indirect.step_supported covered equation
  | @stateful s ambient f rest after op result transition _ =>
    obtain ⟨values,frames,_,_⟩ := Stateful.transition_frame _ _ _ _ _ _ transition
    have functions := Stateful.transition_functions _ _ _ _ _ _ transition
    have active := covered.active {f with code := op.source::after} (List.mem_cons_self ..)
    refine ⟨?_,covered.functions.same functions⟩
    rw [frames]
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun instruction present => active.1 instruction (List.mem_cons_of_mem _ present),active.2⟩
    · exact covered.active item (List.mem_cons_of_mem _ member)

theorem Step.next_simulation_supported {before next : AState} (step : Step before (.next next))
 (typed : CoreTyped before) (covered : SupportedState before) : NextSim before next := by
  cases step with
  | core equation executable => exact (Supported.step_correct before next typed covered equation).2
  | scalar transition => exact Float.transition_simulation _ _ _ _ _ _ _ typed.typed transition

  | indirect equation _ => exact NextSim.counted (Indirect.next_simulation _ _ _ _ _ _ _ _ typed equation) (by decide)
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).2.2

theorem Step.next_owned_supported {bounds : Bounds} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : SupportedState before)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | core equation executable =>
    have fresh := Supported.step_owned typed covered owned.core equation
    exact ⟨fresh.values,core_heap_owned owned.heap fresh.globals equation⟩
  | @scalar s ambient f rest after op result transition =>
    cases transition with
    | next front a b bits values first second effect =>
      have frame := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
      have remaining : ∀ g ∈ rest, FrameOwned bounds g := fun g member => owned.values.2 g (List.mem_cons_of_mem _ member)
      apply stateful_owned_advance (step := rfl) owned.heap (values_owned_nil _) ?_ remaining
      refine ⟨frame.1,values_owned_append.mpr ⟨?_,?_⟩⟩
      · have original := frame.2
        change ValuesOwned bounds f.vals at original
        change f.vals = front ++ op.operands a b at values
        rw [values] at original
        exact (values_owned_append.mp original).1
      · intro value member
        simp only [List.mem_singleton] at member
        subst value
        trivial

  | indirect equation _ => exact Indirect.step_stateful_owned owned equation
  | stateful transition _ => exact stateful_transition_owned _ _ _ _ _ _ _ _ typed owned transition

theorem Step.next_bound_supported {bound : Nat} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : SupportedState before)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | core equation executable => exact Supported.step_bound bound before next typed covered bounded equation
  | scalar transition =>
    cases transition with
    | next front a b bits values first second effect =>
      apply advance_bound bounded rfl
      have frame := bounded.frames _ (List.mem_cons_self ..)
      refine ⟨?_,frame.2⟩
      have size := frame.1
      simp at size ⊢
      omega

  | indirect equation _ => exact Indirect.step_bound bounded equation
  | stateful transition _ => exact Stateful.transition_bound _ _ _ _ _ _ _ _ bounded transition

theorem Step.next_extends_supported {before next : AState} (step : Step before (.next next))
 (typed : CoreTyped before) (covered : SupportedState before) : Extend_store before.store next.store := by
  cases step with
  | core equation executable => exact Supported.step_extends before next typed covered equation
  | scalar transition => cases transition; exact extend_store_refl _ typed.typed.store

  | indirect equation _ => rw [(Indirect.step_metadata equation).1]; exact extend_store_refl _ typed.typed.store
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).2.1

theorem Step.trap_simulation_supported {before : AState} (step : Step before .trap)
 (typed : CoreTyped before) (covered : SupportedState before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | core equation executable => exact Supported.step_trap before typed covered equation
  | scalar transition => exact Float.transition_trap_simulation _ _ _ _ _ _ typed.typed transition

  | indirect equation _ => exact Indirect.trap_simulation _ _ _ _ _ _ _ typed equation
  | stateful transition _ => exact Stateful.transition_trap _ _ _ _ _ _ typed transition

end Itasca.Runtime.SourceMachine.Cumulative

end
