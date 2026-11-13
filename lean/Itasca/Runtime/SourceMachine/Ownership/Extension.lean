import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
Sections, each formerly its own module: Bounds, Numeric, Slice, Core, Extension.
-/

/-! ## Bounds -/

section

namespace Itasca.Runtime.SourceMachine.Ownership

/-- Source function and external references use distinct issued address spaces. -/
structure Bounds where
  functions : Nat
  externs : Nat

/-- Only non-null references carry an ownership obligation. -/
def ValueOwned (bound : Bounds) : val → Prop
  | .REF_FUNC_ADDR address => address < bound.functions
  | .REF_HOST_ADDR address => address < bound.externs
  | _ => True

def ValuesOwned (bound : Bounds) (values : List val) : Prop := ∀ value ∈ values, ValueOwned bound value

def FrameOwned (bound : Bounds) (f : AFrame) : Prop :=
  ValuesOwned bound f.locals ∧ ValuesOwned bound f.vals

def StateOwned (bound : Bounds) (s : AState) : Prop :=
  ValuesOwned bound s.results ∧ ∀ f ∈ s.frames, FrameOwned bound f

private theorem values_subset {bound before after} (bounded : ValuesOwned bound before)
    (subset : ∀ value ∈ after, value ∈ before) : ValuesOwned bound after :=
  fun value member => bounded value (subset value member)

@[simp] theorem values_owned_nil (bound : Bounds) : ValuesOwned bound [] := by simp [ValuesOwned]

@[simp] theorem values_owned_append {bound left right} :
    ValuesOwned bound (left ++ right) ↔ ValuesOwned bound left ∧ ValuesOwned bound right := by
  simp only [ValuesOwned, List.mem_append]
  constructor
  · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hl, hr⟩ v (hv | hv)
    · exact hl v hv
    · exact hr v hv

@[simp] theorem values_owned_cons {bound value rest} :
    ValuesOwned bound (value :: rest) ↔ ValueOwned bound value ∧ ValuesOwned bound rest := by
  simp [ValuesOwned]

 theorem ValuesOwned.take {bound values} (bounded : ValuesOwned bound values) (count : Nat) :
    ValuesOwned bound (values.take count) := values_subset bounded (fun _ member => List.mem_of_mem_take member)

 theorem ValuesOwned.drop {bound values} (bounded : ValuesOwned bound values) (count : Nat) :
    ValuesOwned bound (values.drop count) := values_subset bounded (fun _ member => List.mem_of_mem_drop member)

 theorem ValuesOwned.set {bound values value} (bounded : ValuesOwned bound values)
    (allowed : ValueOwned bound value) (index : Nat) : ValuesOwned bound (values.set index value) := by
  induction values generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using values_owned_cons.mpr ⟨allowed, (values_owned_cons.mp bounded).2⟩
    | succ index =>
      simpa using values_owned_cons.mpr ⟨(values_owned_cons.mp bounded).1, ih (values_owned_cons.mp bounded).2 index⟩

 theorem ValuesOwned.pop {bound values rest value} (bounded : ValuesOwned bound values)
    (popped : SourceMachine.pop values = some (rest, value)) : ValuesOwned bound rest ∧ ValueOwned bound value := by
  unfold SourceMachine.pop at popped
  split at popped
  · contradiction
  next last tail equal =>
    have reversed : values = (last :: tail).reverse := by rw [← equal, List.reverse_reverse]
    rw [reversed, List.reverse_cons] at bounded
    cases popped
    simpa using bounded

 theorem default_value_ownership {bound ty value} (created : defaultValue ty = some value) :
    ValueOwned bound value := by
  cases ty <;> simp [defaultValue] at created <;> subst value <;> trivial

 theorem default_locals_ownership {bound locals values} (created : defaultLocals locals = some values) :
    ValuesOwned bound values := by
  induction locals generalizing values with
  | nil => simp [defaultLocals] at created; subst values; simp
  | cons item locals ih =>
    cases item with
    | LOCAL ty =>
      cases first : defaultValue ty with
      | none => simp [defaultLocals, first] at created
      | some value =>
        cases tail : defaultLocals locals with
        | none => simp [defaultLocals, first, tail] at created
        | some rest =>
          simp [defaultLocals, first, tail] at created
          subst values
          exact values_owned_cons.mpr ⟨default_value_ownership first, ih tail⟩

 theorem ownership_advance {bound s f rest next}
    (results : ValuesOwned bound s.results) (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : advance s f rest = .next next) : StateOwned bound next := by
  cases step
  exact ⟨results, by simpa using And.intro frame frames⟩

 theorem ownership_return {bound s f rest next}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : returnFrame s f rest = .next next) : StateOwned bound next := by
  unfold returnFrame at step
  split at step
  · split at step
    · cases step
      exact ⟨frame.2.drop _, by simp⟩
    next original caller callers =>
      have callerBound := frames caller (by simp)
      apply ownership_advance (step := step) results
      · exact ⟨callerBound.1, values_owned_append.mpr ⟨callerBound.2, frame.2.drop _⟩⟩
      · exact fun item member => frames item (by simp [member])
  · contradiction

 theorem ownership_branch {bound s f rest next depth}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : branch s f rest depth = .next next) : StateOwned bound next := by
  unfold branch at step
  split at step
  · contradiction
  next target found =>
    split at step
    · apply ownership_advance (step := step) results ?_ frames
      exact ⟨frame.1, values_owned_append.mpr ⟨frame.2.take _, frame.2.drop _⟩⟩
    · contradiction

 theorem ownership_enter {bound s f rest next ty body after loop}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : enterLabel s f rest ty body after loop = .next next) : StateOwned bound next := by
  simp only [enterLabel] at step
  repeat' first | split at step | contradiction
  all_goals
    apply ownership_advance (step := step) results ?_ frames
    exact frame

 theorem ownership_call {bound s f rest next index after}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : call s f rest index after = .next next) : StateOwned bound next := by
  simp only [call] at step
  repeat' first | split at step | contradiction
  cases step
  refine ⟨results, ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨⟨values_owned_append.mpr ⟨frame.2.drop _, ?_⟩, values_owned_nil _⟩, ⟨frame.1, frame.2.take _⟩, frames⟩
  apply default_locals_ownership
  assumption

end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Numeric -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open Itasca.Runtime.SourceMachine.Numeric

theorem finish_ownership {bound s f rest next after front op a b}
    (results : ValuesOwned bound s.results)
    (locals : ValuesOwned bound f.locals) (values : ValuesOwned bound front)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : finish s f rest after front op a b = .next next) :
    StateOwned bound next := by
  unfold finish at step
  split at step
  · contradiction
  · apply ownership_advance (step := step) results ?_ frames
    exact ⟨locals, values_owned_append.mpr ⟨values, by simp [ValuesOwned, ValueOwned, integerVal]⟩⟩

theorem transition_ownership {bound s f rest next after op}
    (results : ValuesOwned bound s.results)
    (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : transition s f rest after op = .next next) :
    StateOwned bound next := by
  unfold transition at step
  split at step
  · contradiction
  next front right first =>
    have frontBound := (frame.2.pop first).1
    split at step
    · contradiction
    next bits integer =>
      split at step
      · exact finish_ownership results frame.1 frontBound frames step
      · split at step
        · contradiction
        next front left second =>
          split at step
          · contradiction
          · exact finish_ownership results frame.1 (frontBound.pop second).1 frames step
end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Slice -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec

theorem instruction_ownership (bound : Bounds) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState) (results : List val)
    (allowed : PureHead op) (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (resultBound : ValuesOwned bound results)
    (step : astep ⟨s, ambient, {f with code := op :: after} :: rest, results⟩ = .next next) :
    StateOwned bound next := by
  cases allowed with
  | call index => cases index; exact ownership_call frame frames resultBound step
  | ret => exact ownership_return frame frames resultBound step
  | br depth => cases depth; exact ownership_branch frame frames resultBound step
  | block ty body => exact ownership_enter frame frames resultBound step
  | loop ty body => exact ownership_enter frame frames resultBound step
  | numeric descriptor =>
    cases descriptor
    all_goals
      have localsBound := frame.1
      have valuesOwned := frame.2
      simp only [Numeric.Instruction.source, Numeric.Conversion.source, Numeric.decodeInstruction, astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
      repeat' first
        | solve | exact transition_ownership resultBound frame frames step
        | split at step
        | contradiction
      all_goals
        apply ownership_advance (step := step) resultBound ?_ frames
        constructor
        · first
          | exact localsBound
          | apply ValuesOwned.set localsBound; aesop (add safe forward ValuesOwned.pop)
        · first
          | solve | aesop (add safe forward ValuesOwned.pop)
          | apply values_owned_append.mpr; constructor
            · aesop (add safe forward ValuesOwned.pop)
            · apply values_owned_cons.mpr; constructor
              · first
                | trivial
                | solve | aesop (add safe forward ValuesOwned.pop)
                | apply localsBound; apply List.mem_of_getElem?; assumption
              · exact values_owned_nil _
  | _ =>
    have localsBound := frame.1
    have valuesOwned := frame.2
    simp only [astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply ownership_advance (step := step) resultBound ?_ frames
      constructor
      · first
        | exact localsBound
        | apply ValuesOwned.set localsBound; aesop (add safe forward ValuesOwned.pop)
      · first
        | solve | aesop (add safe forward ValuesOwned.pop)
        | apply values_owned_append.mpr; constructor
          · aesop (add safe forward ValuesOwned.pop)
          · apply values_owned_cons.mpr; constructor
            · first
              | trivial
              | solve | aesop (add safe forward ValuesOwned.pop)
              | apply localsBound; apply List.mem_of_getElem?; assumption
            · exact values_owned_nil _

end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Core -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec

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
    refine ⟨frame.1,values_owned_append.mpr ⟨?_,?_⟩⟩
    · aesop (add safe forward ValuesOwned.pop)
    · apply values_owned_cons.mpr
      constructor
      · aesop (add safe forward ValuesOwned.pop)
      · exact values_owned_nil _

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
      exact owned_advance step globals results ⟨frame.1,values_owned_append.mpr
        ⟨frame.2,values_owned_cons.mpr ⟨globals object (List.mem_of_getElem? found),values_owned_nil _⟩⟩⟩ frames

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
      refine ⟨frame.1,values_owned_append.mpr ⟨owned,?_⟩⟩
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
    (covered : CoreHead op) (typed : FrameTyped s {f with code := op :: after} [])
    (globals : GlobalsOwned bounds s) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.instruction s ambient f rest op after = .next next) : CoreOwned bounds next := by
  cases covered with
  | pure pure =>
    rw [Core.instruction_slice s ambient f rest op after pure typed] at step
    exact ⟨instruction_ownership bounds s ambient f rest op after next [] pure frame frames (values_owned_nil _) step,
      by rw [astep_store step]; exact globals⟩
  | const ty value =>
    exact owned_advance step globals (values_owned_nil _) ⟨frame.1,
      values_owned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned]⟩⟩ frames
  | select => exact select_owned globals (values_owned_nil _) frame frames step
  | global_get index => cases index; exact global_get_owned globals (values_owned_nil _) frame frames step
  | global_set index => cases index; exact global_set_owned globals (values_owned_nil _) frame frames step
  | load op argument =>
    rw [Core.instruction_load] at step
    exact load_owned globals (values_owned_nil _) frame frames step
  | store op argument =>
    rw [Core.instruction_store] at step
    exact store_owned globals (values_owned_nil _) frame frames step

end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Extension -/

section

namespace Itasca.Runtime.SourceMachine.Ownership

/-- Publication may enlarge either reference namespace. Existing references
remain owned only when both address bounds are retained. -/
structure Bounds.Extends (before after : Bounds) : Prop where
  functions : before.functions ≤ after.functions
  externs : before.externs ≤ after.externs

theorem ValueOwned.extend {before after value} (extension : before.Extends after)
    (owned : ValueOwned before value) : ValueOwned after value := by
  cases value <;> try trivial
  · exact owned.trans_le extension.functions
  · exact owned.trans_le extension.externs

theorem ValuesOwned.extend {before after values} (extension : before.Extends after)
    (owned : ValuesOwned before values) : ValuesOwned after values :=
  fun value member => (owned value member).extend extension

theorem FrameOwned.extend {before after frame} (extension : before.Extends after)
    (owned : FrameOwned before frame) : FrameOwned after frame :=
  ⟨owned.1.extend extension,owned.2.extend extension⟩

theorem StateOwned.extend {before after source} (extension : before.Extends after)
    (owned : StateOwned before source) : StateOwned after source :=
  ⟨owned.1.extend extension,fun frame member => (owned.2 frame member).extend extension⟩

/-- A resumed caller retains its locals and prefix operands; only the checked
host result values are added. Older suspended callers retain their ownership. -/
theorem StateOwned.host_return {before after : Bounds} {s target : store} {ambient : frame}
    {caller : AFrame} {rest : List AFrame} {front args returned : List val} {code : List instr}
    (extension : before.Extends after)
    (owned : StateOwned before ⟨s,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++args) (results : ValuesOwned after returned) :
    StateOwned after ⟨target,ambient,{caller with code:=code,vals:=front++returned}::rest,[]⟩ := by
  have previous := owned.extend extension
  have current := previous.2 caller (List.mem_cons_self ..)
  refine ⟨values_owned_nil _,?_⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨current.1,values_owned_append.mpr ⟨?_,results⟩⟩
    have operands := current.2
    rw [split] at operands
    exact (values_owned_append.mp operands).1
  · exact previous.2 item (List.mem_cons_of_mem _ member)
end Itasca.Runtime.SourceMachine.Ownership

end
