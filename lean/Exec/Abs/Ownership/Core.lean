import Exec.Abs.Ownership.Slice
import Exec.Abs.Core.Pure
import Exec.Abs.Core.PureMetadata
namespace Exec.Abs.Ownership
open SpecExt Exec.Spec

def GlobalsOwned (bounds : Bounds) (s : _root_.store) : Prop :=
  ∀ object ∈ s.GLOBALS, ValueOwned bounds object.VALUE

structure CoreOwned (bounds : Bounds) (s : AState) : Prop where
  values : StateOwned bounds s
  globals : GlobalsOwned bounds s.store

theorem GlobalsOwned.write {bounds s f index value}
    (globals : GlobalsOwned bounds s) (owned : ValueOwned bounds value) :
    GlobalsOwned bounds (Spec.globalWrite s f index value) := by
  apply Spec.Segment.forall_modify _ _ _ _ globals
  intro object present
  exact owned

theorem owned_advance {bounds s f rest next}
    (step : advance s f rest = .next next)
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item) : CoreOwned bounds next := by
  exact ⟨ownership_advance results frame frames step, by cases step; exact globals⟩

theorem select_owned {bounds s f rest next after}
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.select s f rest after = .next next) : CoreOwned bounds next := by
  have values := frame.2
  unfold Core.select at step
  repeat' first | split at step | contradiction
  all_goals
    apply owned_advance step globals results ?_ frames
    refine ⟨frame.1,valuesOwned_append.mpr ⟨?_,?_⟩⟩
    · aesop (add safe forward ValuesOwned.pop)
    · apply valuesOwned_cons.mpr
      constructor
      · aesop (add safe forward ValuesOwned.pop)
      · exact valuesOwned_nil _

theorem global_get_owned {bounds s f rest next index after}
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.globalGet s f rest index after = .next next) : CoreOwned bounds next := by
  unfold Core.globalGet at step
  split at step
  · contradiction
  next address mapped =>
    split at step
    · contradiction
    next object found =>
      exact owned_advance step globals results ⟨frame.1,valuesOwned_append.mpr
        ⟨frame.2,valuesOwned_cons.mpr ⟨globals object (List.mem_of_getElem? found),valuesOwned_nil _⟩⟩⟩ frames

theorem global_set_owned {bounds s f rest next index after}
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.globalSet s f rest index after = .next next) : CoreOwned bounds next := by
  unfold Core.globalSet at step
  split at step
  next front value address popped mapped =>
    have owned := frame.2.pop popped
    repeat' first | split at step | contradiction
    all_goals exact owned_advance step (globals.write owned.2) results ⟨frame.1,owned.1⟩ frames
  · contradiction

theorem load_owned {bounds s f rest next after op argument}
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.load s f rest after op argument = .next next) : CoreOwned bounds next := by
  unfold Core.load at step
  dsimp only at step
  split at step
  next front address memoryAddress popped mapped =>
    have owned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply owned_advance step globals results ?_ frames
      refine ⟨frame.1,valuesOwned_append.mpr ⟨owned,?_⟩⟩
      cases op <;> simp [Memory.Load.value,ValuesOwned,ValueOwned]
  · contradiction

theorem store_owned {bounds s f rest next after op argument}
    (globals : GlobalsOwned bounds s.store)
    (results : ValuesOwned bounds s.results) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.store s f rest after op argument = .next next) : CoreOwned bounds next := by
  unfold Core.store at step
  dsimp only at step
  split at step
  next remaining ty value memoryAddress popped mapped =>
    have owned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply owned_advance step globals results ?_ frames
      refine ⟨frame.1,?_⟩
      aesop (add safe forward ValuesOwned.pop)
  · contradiction

theorem instruction_owned (bounds : Bounds) (s : _root_.store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreInstr op) (typed : FrameTyped s {f with code := op :: after} [])
    (globals : GlobalsOwned bounds s) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.instruction s ambient f rest op after = .next next) : CoreOwned bounds next := by
  cases covered with
  | slice pure =>
    rw [Core.instruction_slice s ambient f rest op after pure typed] at step
    exact ⟨instruction_ownership bounds s ambient f rest op after next [] pure frame frames (valuesOwned_nil _) step,
      by rw [astep_store step]; exact globals⟩
  | constant ty value =>
    exact owned_advance step globals (valuesOwned_nil _) ⟨frame.1,
      valuesOwned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned]⟩⟩ frames
  | select => exact select_owned globals (valuesOwned_nil _) frame frames step
  | global_get index => cases index; exact global_get_owned globals (valuesOwned_nil _) frame frames step
  | global_set index => cases index; exact global_set_owned globals (valuesOwned_nil _) frame frames step
  | load op argument =>
    rw [Core.instruction_load] at step
    exact load_owned globals (valuesOwned_nil _) frame frames step
  | store op argument =>
    rw [Core.instruction_store] at step
    exact store_owned globals (valuesOwned_nil _) frame frames step
  | block ty body valid =>
    have pureStep : astep ⟨s,ambient,{f with code := .BLOCK ty body :: after} :: rest,[]⟩ = .next next := step
    exact ⟨ownership_enter (step := step) frame frames (valuesOwned_nil _), by rw [astep_store pureStep]; exact globals⟩
  | loop ty body valid =>
    have pureStep : astep ⟨s,ambient,{f with code := .LOOP ty body :: after} :: rest,[]⟩ = .next next := step
    exact ⟨ownership_enter (step := step) frame frames (valuesOwned_nil _), by rw [astep_store pureStep]; exact globals⟩
  | ifelse ty yes no yesValid noValid =>
    have pureStep : astep ⟨s,ambient,{f with code := .IFELSE ty yes no :: after} :: rest,[]⟩ = .next next := step
    refine ⟨?_, by rw [astep_store pureStep]; exact globals⟩
    simp only [Core.instruction,astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply ownership_advance (step := step) (valuesOwned_nil _) ?_ frames
      have values := frame.2
      exact ⟨frame.1, by aesop (add safe forward ValuesOwned.pop)⟩

theorem step_owned {bounds : Bounds} {s next : AState}
    (typed : CoreTyped s) (covered : CoreState s) (owned : CoreOwned bounds s)
    (step : Core.step s = .next next) : CoreOwned bounds next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have first := owned.values.2 frame (by simp)
    have remaining : ∀ item ∈ rest, FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
    have allowed := (covered.active frame (by simp)).1
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
        exact instruction_owned bounds store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next
          (allowed op (by simp)) frameTyped owned.globals first remaining step
end Exec.Abs.Ownership
