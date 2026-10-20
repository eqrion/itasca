import Exec.Theorems.Host.Callbacks.StoreCallbackSemantics
import Exec.Interp.Control.LoopPrefix

/-! Resumable host-local control for the checked callback class. The pending
call and each committed store are observable before the next tick. This model
covers host loops; suspended/nested Wasm needs additional combined transitions. -/
namespace Exec.Theorems.OpenHostControl
open Aeneas Aeneas.Std

inductive Instruction where
  | returned (values : Slice PureCallbacks.Literal)
  | trapped
  | jump (target : Nat)
  | branch (condition : Bool) (yes no : Nat)
  | action (segment : StoreCallbacks.Program) (next : Nat)

abbrev Code := List Instruction

structure State (M : Type) where
  pc : Nat
  store : runtime.store.Store M
  identity : U64
  arguments : Slice runtime.Value

abbrev Reply (M : Type) := StoreCallbacks.Reply M

def literalValues (values : Slice PureCallbacks.Literal) : Slice runtime.Value :=
  Slice.from (values.val.map PureCallbacks.Literal.value) (by simpa using values.property)

/-- One executable tick. Finite checked actions finish before control proceeds;
no tick invokes an arbitrary synchronous native callback. -/
def tick {M : Type} (memory : runtime.platform.MemoryBuffer M) (code : Code) (state : State M) :
    Result (ControlFlow (State M) (Reply M)) :=
  match code[state.pc]? with
  | none | some .trapped => .ok (.done (.Err .Trap,state.store,Slice.new _))
  | some (.returned values) => .ok (.done (.Ok (),state.store,literalValues values))
  | some (.jump target) => .ok (.cont {state with pc := target})
  | some (.branch condition yes no) => .ok (.cont {state with pc := if condition then yes else no})
  | some (.action segment next) => do
    let answer ← segment.run memory state.store
    match answer.1 with
    | .Ok () => .ok (.cont {state with pc := next,store := answer.2.1})
    | .Err _ => .ok (.done answer)

/-- Independent host-local control and checked operation semantics. Each
continuing state retains the pending call identity and immutable arguments. -/
inductive Transition {M : Type} (code : Code) (state : State M) : ControlFlow (State M) (Reply M) → Prop
  | missing (selected : code[state.pc]? = none) :
      Transition code state (.done (.Err .Trap,state.store,Slice.new _))
  | trapped (selected : code[state.pc]? = some .trapped) :
      Transition code state (.done (.Err .Trap,state.store,Slice.new _))
  | returned (values : Slice PureCallbacks.Literal) (selected : code[state.pc]? = some (.returned values)) :
      Transition code state (.done (.Ok (),state.store,literalValues values))
  | jump (target : Nat) (selected : code[state.pc]? = some (.jump target)) :
      Transition code state (.cont {state with pc := target})
  | branch (condition : Bool) (yes no : Nat) (selected : code[state.pc]? = some (.branch condition yes no)) :
      Transition code state (.cont {state with pc := if condition then yes else no})
  | action {segment next after values} (selected : code[state.pc]? = some (.action segment next))
      (effect : StoreCallbacks.Returns segment state.store (.Ok ()) after values) :
      Transition code state (.cont {state with pc := next,store := after})
  | rejected {segment next error after values} (selected : code[state.pc]? = some (.action segment next))
      (effect : StoreCallbacks.Returns segment state.store (.Err error) after values.val) :
      Transition code state (.done (.Err error,after,values))

/-- Actual ticks return normally and refine the independent local semantics. -/
theorem tick_refines {M : Type} (memory : runtime.platform.MemoryBuffer M) (code : Code) (state : State M) :
    tick memory code state ⦃ out => Transition code state out ⦄ := by
  unfold tick
  cases selected : code[state.pc]? with
  | none => exact WP.spec.ret (.missing selected)
  | some instruction =>
    cases instruction with
    | trapped => exact WP.spec.ret (.trapped selected)
    | returned values => exact WP.spec.ret (.returned values selected)
    | jump target => exact WP.spec.ret (.jump target selected)
    | branch condition yes no => exact WP.spec.ret (.branch condition yes no selected)
    | action segment next =>
      simp only [tick,selected]
      obtain ⟨⟨status,after,values⟩,actual,source⟩ := WP.spec_imp_exists (segment.refines memory state.store)
      rw [actual,bind_ok]
      cases status with
      | Ok result =>
        cases result
        exact WP.spec.ret (.action selected source)
      | Err error => exact WP.spec.ret (.rejected selected source)

structure Effect {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before after : runtime.store.Store M) : Prop where
  invariant : ExecutableInv view code after
  metadata : Interp.FrameStorePrefix before after
  extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)
  externs : after.externs = before.externs

theorem Effect.refl {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) : Effect view code store store :=
  ⟨held,.refl _,Spec.extend_store_refl _ held.well_formed,rfl⟩

theorem Effect.trans {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before middle after : runtime.store.Store M} (first : Effect view code before middle)
    (second : Effect view code middle after) : Effect view code before after :=
  ⟨second.invariant,first.metadata.trans second.metadata,
    Spec.extend_store_trans first.extension second.extension,second.externs.trans first.externs⟩

def outputStore {M : Type} : ControlFlow (State M) (Reply M) → runtime.store.Store M
  | .cont next => next.store
  | .done answer => answer.2.1

/-- Every executable prefix retains the public certificates and the exact
pending-call data; completed results remain issued. -/
theorem tick_preserves {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (state : State M)
    (held : ExecutableInv view code state.store) :
    tick memory program state ⦃ out => Effect view code state.store (outputStore out) ∧
      match out with
      | .cont next => next.identity = state.identity ∧ next.arguments = state.arguments
      | .done answer => ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄ := by
  unfold tick
  cases selected : program[state.pc]? with
  | none => exact WP.spec.ret ⟨.refl held,by simp⟩
  | some instruction =>
    cases instruction with
    | trapped => exact WP.spec.ret ⟨.refl held,by simp⟩
    | returned values =>
      exact WP.spec.ret ⟨.refl held,(PureCallbacks.Program.returned values).issued state.store⟩
    | jump target => exact WP.spec.ret ⟨.refl held,rfl,rfl⟩
    | branch condition yes no => exact WP.spec.ret ⟨.refl held,rfl,rfl⟩
    | action segment next =>
      simp only [tick,selected]
      obtain ⟨⟨status,after,values⟩,actual,fresh,metadata,extension,externs,issued⟩ :=
        WP.spec_imp_exists (segment.correct memory view code state.store held)
      rw [actual,bind_ok]
      cases status with
      | Ok result =>
        cases result
        exact WP.spec.ret ⟨⟨fresh,metadata,extension,externs⟩,rfl,rfl⟩
      | Err error => exact WP.spec.ret ⟨⟨fresh,metadata,extension,externs⟩,issued⟩

/-- A syntactic ranking proves termination of graph control. Checked finite
segments have their own implementation termination proof. -/
def Ranked (program : Code) (rank : Nat → Nat) : Prop :=
  ∀ (pc : Nat) (instruction : Instruction), program[pc]? = some instruction →
    match instruction with
    | .jump next | .action _ next => rank next < rank pc
    | .branch condition yes no => rank (if condition then yes else no) < rank pc
    | .returned _ | .trapped => True

theorem Transition.decreases {M : Type} {program : Code} {rank : Nat → Nat}
    (ranked : Ranked program rank) {state next : State M}
    (source : Transition program state (.cont next)) : rank next.pc < rank state.pc := by
  cases source with
  | jump target selected => exact ranked _ _ selected
  | branch condition yes no selected => exact ranked _ _ selected
  | action selected _ => exact ranked _ _ selected

/-- The synchronous implementation is the Aeneas loop over the same actual
ticks. Divergence is interpreted via its productive prefixes below. -/
def run {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code) (state : State M) : Result (Reply M) :=
  loop (tick memory program) state

/-- Ranking, rather than an assumed native callback-normality law, proves
ordinary return of this executable callback implementation. -/
theorem run_terminates {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (rank : Nat → Nat) (ranked : Ranked program rank) (state : State M) :
    run memory program state ⦃ _ => True ⦄ := by
  have terminate : ∀ bound current, rank current.pc = bound → run memory program current ⦃ _ => True ⦄ := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current equal
      obtain ⟨out,actual,source⟩ := WP.spec_imp_exists (tick_refines memory program current)
      unfold run
      rw [loop.eq_def,actual,bind_ok]
      cases out with
      | done answer => exact WP.spec.ret trivial
      | cont next => exact ih _ (by rw [← equal]; exact source.decreases ranked) next rfl
  exact terminate _ state rfl

inductive ReturnedControl {M : Type} (program : Code) : State M → Reply M → Prop
  | done {state answer} (source : Transition program state (.done answer)) : ReturnedControl program state answer
  | next {state middle answer} (source : Transition program state (.cont middle))
      (tail : ReturnedControl program middle answer) : ReturnedControl program state answer

/-- A finite trace of actual ticks retains each independent host-local/API
transition. It does not discard pending activity before the final reply. -/
theorem normal_trace_refines {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    {count state answer} (trace : Interp.NormalTrace (tick memory program) count state answer) :
    ReturnedControl program state answer := by
  induction trace with
  | @done current answer actual =>
    have source := tick_refines memory program current
    rw [actual,WP.spec_ok] at source
    exact .done source
  | @next count current next answer actual tail ih =>
    have source := tick_refines memory program current
    rw [actual,WP.spec_ok] at source
    exact .next source ih

/-- Divergence of the synchronous implementation gives one coherent infinite
host-control execution. It is not relabeled as Wasm divergence. -/
theorem run_infinite_control {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (state : State M) (divergent : run memory program state = .div) :
    ∃ states : Nat → State M, states 0 = state ∧
      ∀ n, Transition program (states n) (.cont (states (n+1))) := by
  obtain ⟨states,first,edges⟩ := Interp.loop_divergent_stream (tick memory program) (fun _ => True)
    (fun state _ => WP.spec_mono (tick_refines memory program state) (fun _ _ => by split <;> trivial))
    state trivial divergent
  refine ⟨states,first,?_⟩
  intro n
  have source := tick_refines memory program (states n)
  rw [(edges n).2.1,WP.spec_ok] at source
  exact source

/-- The cumulative prefix invariant records effects already committed and
keeps the pending call observable before any eventual return or divergence. -/
def PrefixInvariant {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (initial current : State M) : Prop :=
  Effect view code initial.store current.store ∧
    current.identity = initial.identity ∧ current.arguments = initial.arguments

private theorem tick_prefix {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (initial current : State M)
    (held : PrefixInvariant view code initial current) :
    tick memory program current ⦃ out =>
      match out with
      | .cont next => PrefixInvariant view code initial next
      | .done _ => True ⦄ := by
  apply WP.spec_mono (tick_preserves memory program view code current held.1.invariant)
  intro out preserved
  cases out with
  | cont next =>
    exact ⟨held.1.trans preserved.1,preserved.2.1.trans held.2.1,preserved.2.2.trans held.2.2⟩
  | done answer => trivial

/-- Returning and divergent synchronous executions share the same productive
body proof. Every actual return has a finite control trace and retained effects. -/
theorem run_safe {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (state : State M)
    (held : ExecutableInv view code state.store) :
    run memory program state ⦃ answer => ReturnedControl program state answer ∧
      Effect view code state.store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄div := by
  have bodyTotal : ∀ current, PrefixInvariant view code state current →
      tick memory program current ⦃ out =>
        match out with
        | .cont next => PrefixInvariant view code state next
        | .done answer => Effect view code state.store answer.2.1 ∧
            ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄ := by
    intro current valid
    apply WP.spec_mono (tick_preserves memory program view code current valid.1.invariant)
    intro out preserved
    cases out with
    | cont next => exact ⟨valid.1.trans preserved.1,preserved.2.1.trans valid.2.1,preserved.2.2.trans valid.2.2⟩
    | done answer => exact ⟨valid.1.trans preserved.1,preserved.2⟩
  have safe := Interp.loop_trace_dspec (tick memory program) (PrefixInvariant view code state)
    (fun answer => Effect view code state.store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value)
    (fun current valid => WP.spec_mono (bodyTotal current valid)
      (by intro out preserved; cases out <;> exact preserved)) state ⟨.refl held,rfl,rfl⟩
  exact WP.dspec_mono safe (fun answer ⟨count,trace,effect⟩ => ⟨normal_trace_refines memory program trace,effect⟩)

/-- The ordinary callback interface delegates to the same resumable ticks.
No universal callback-normality contract is asserted for graphs with loops. -/
def platform {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Code) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ := do
    let answer ← run memory (select identity args) ⟨0,store,identity,args⟩
    .ok (answer.1,token,answer.2.1,answer.2.2)

/-- A syntactically ranked graph supplies the returning-host law from its
implementation. Unranked graphs instead use the prefix/divergence contracts. -/
theorem ranked_sound {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Code)
    (ranking : ∀ identity args, ∃ rank, Ranked (select identity args) rank)
    (view : M → Slice U8) (code : Store.CodeInterpretation) :
    Platform.HostSound (platform memory select) (ExecutableInv view code) (Store.decodeStore view code) := by
  apply Platform.HostSound.of_invariant (fun _ held => held.source_typed)
  intro token store identity args results held
  obtain ⟨rank,ranked⟩ := ranking identity args
  obtain ⟨answer,actual,_⟩ := WP.spec_imp_exists
    (run_terminates memory (select identity args) rank ranked ⟨0,store,identity,args⟩)
  have safe := run_safe memory (select identity args) view code ⟨0,store,identity,args⟩ held
  rw [actual,WP.dspec_ok] at safe
  simp only [platform,actual,bind_ok]
  exact WP.spec.ret ⟨safe.2.1.invariant,safe.2.1.extension⟩

/-- Every finite observable prefix of a diverging implementation retains
source typing, the committed extension, and pending-call data. The trace is a
trace of actual ticks, rather than information inferred from bare `.div`. -/
theorem divergent_prefix_typed {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (state : State M)
    (held : ExecutableInv view code state.store) (count : Nat)
    (divergent : run memory program state = .div) :
    ∃ last, Interp.ContinuingTrace (tick memory program) count state last ∧
      PrefixInvariant view code state last ∧ Store_ok (Store.decodeStore view code last.store) ∧
      run memory program last = .div := by
  obtain ⟨last,trace,preserved,continues⟩ := Interp.loop_divergent_prefix (tick memory program)
    (PrefixInvariant view code state) (fun current valid => WP.spec_mono (tick_prefix memory program view code state current valid)
      (by intro out preserved; cases out <;> exact preserved))
    count state ⟨.refl held,rfl,rfl⟩ divergent
  exact ⟨last,trace,preserved,preserved.1.invariant.source_typed,continues⟩

/-- One productive infinite source host-control stream retains every prefix's
store effects and source typing under the checked implementation. -/
theorem infinite_control_typed {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (state : State M)
    (held : ExecutableInv view code state.store) (divergent : run memory program state = .div) :
    ∃ states : Nat → State M, states 0 = state ∧ ∀ n,
      PrefixInvariant view code state (states n) ∧ Store_ok (Store.decodeStore view code (states n).store) ∧
      Transition program (states n) (.cont (states (n+1))) := by
  obtain ⟨states,first,edges⟩ := Interp.loop_divergent_stream (tick memory program)
    (PrefixInvariant view code state) (fun current valid => WP.spec_mono (tick_prefix memory program view code state current valid)
      (by intro out preserved; cases out <;> exact preserved))
    state ⟨.refl held,rfl,rfl⟩ divergent
  refine ⟨states,first,?_⟩
  intro n
  have source := tick_refines memory program (states n)
  rw [(edges n).2.1,WP.spec_ok] at source
  exact ⟨(edges n).1,(edges n).1.1.invariant.source_typed,source⟩

/-- A directly implemented host-local loop has an infinite actual tick stream. -/
theorem host_loop_diverges {M : Type} (memory : runtime.platform.MemoryBuffer M) (state : State M)
    (atStart : state.pc = 0) : run memory [.jump 0] state = .div := by
  apply Interp.loop_diverges_of_stream (tick memory [.jump 0]) (fun _ => state)
  intro n
  have same : {state with pc := 0} = state := by cases state; simp_all
  simp [tick,atStart,same]

end Exec.Theorems.OpenHostControl
