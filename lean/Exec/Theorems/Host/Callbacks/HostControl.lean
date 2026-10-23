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

/-- The synchronous implementation is the Aeneas loop over the same actual
ticks. Divergence is interpreted via its productive prefixes below. -/
def run {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Code) (state : State M) : Result (Reply M) :=
  loop (tick memory program) state

/-- The ordinary callback interface delegates to the same resumable ticks.
No universal callback-normality contract is asserted for graphs with loops. -/
def platform {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Code) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ := do
    let answer ← run memory (select identity args) ⟨0,store,identity,args⟩
    .ok (answer.1,token,answer.2.1,answer.2.2)

/-- A directly implemented host-local loop has an infinite actual tick stream. -/
theorem host_loop_diverges {M : Type} (memory : runtime.platform.MemoryBuffer M) (state : State M)
    (atStart : state.pc = 0) : run memory [.jump 0] state = .div := by
  apply Interp.loop_diverges_of_stream (tick memory [.jump 0]) (fun _ => state)
  intro n
  have same : {state with pc := 0} = state := by cases state; simp_all
  simp [tick,atStart,same]

end Exec.Theorems.OpenHostControl
