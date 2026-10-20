import Exec.Theorems.Host.Open.Driver.CallTask
import Exec.Theorems.Host.Open.Driver.HostEffects
import Exec.Theorems.Host.Open.Driver.RootInput
import Exec.Spec.Typing.EmptyFrameTyping
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

def InvokeTask {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : InvokePhase M Unit → Prop
  | .done answer => answer.2.2.1=store ∧ ∃error,answer.1=.Err error
  | .waiting phase root _ => ∃signature,CallTask memory view code store root signature phase

theorem RootInvokeReady.task {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {ambient : frame} {root : runtime.FuncAddr} {signature : Itasca.types.FuncType} {args : List val}
    {phase : InvokePhase M Unit} (held : ExecutableInv view code store) (ambientWf : wf_frame ambient)
    (metadata : RootMetadata store root signature) (guard : RootInvokeReady view code store ambient root signature args phase) :
    InvokeTask memory view code store phase := by
  cases guard with
  | rejected answer error status sameStore => exact ⟨sameStore,error,status⟩
  | waiting phase results ready => exact ⟨signature,ready.task memory held ambientWf metadata⟩

def ModeGuard {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Mode M → Prop
  | .host _ => True
  | .hostReturn _ values => ∀value∈values.val,Store.IssuedValue store value
  | .preparing phase => InvokeTask memory view code store phase
  | .wasm exec status root _ => ∃signature,WasmTask view code store exec status root signature
  | .invokeReturn answer => answer.2.2.1=store ∧
      (answer.1=.Ok () → ∀value∈answer.2.2.2.2.val,Store.IssuedValue store value)

def StackGuard {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : List Continuation → Prop
  | [] => True
  | .host _ _::tail => StackGuard memory view code store tail
  | .wasm exec address base root _::tail =>
      (∃signature,SavedWasm memory view code store exec address base root signature) ∧ StackGuard memory view code store tail

theorem StackGuard.extend {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {beforeCode afterCode : Store.CodeInterpretation} {before after : runtime.store.Store M} {stack : List Continuation}
    (held : StackGuard memory view beforeCode before stack) (effect : ReentrantCallbacks.Effect view beforeCode before afterCode after) :
    StackGuard memory view afterCode after stack := by
  induction stack with
  | nil => trivial
  | cons frame tail ih =>
    cases frame with
    | host host next => exact ih held
    | wasm exec address base root results =>
      obtain ⟨signature,saved⟩ := held.1
      exact ⟨⟨signature,saved.extend effect⟩,ih held.2⟩

def StateGuard {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (state : State M) : Prop :=
  ExecutableInv view code state.store ∧ ModeGuard memory view code state.store state.mode ∧
    StackGuard memory view code state.store state.stack

def Outcome.store {M : Type} : Outcome M → runtime.store.Store M
  | .host answer _ => answer.2.1
  | .invocation answer _ => answer.2.2.1

def OutcomeGuard {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation) (out : Outcome M) : Prop :=
  ExecutableInv view code out.store ∧ match out with
    | .host answer _ => ∀value∈answer.2.2.val,Store.IssuedValue out.store value
    | .invocation answer _ => answer.1=.Ok () → ∀value∈answer.2.2.2.2.val,Store.IssuedValue out.store value

def GuardedOutput {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : ControlFlow (State M) (Outcome M) → Prop
  | .cont next => ∃afterCode,ReentrantCallbacks.Effect view code store afterCode next.store ∧ StateGuard memory view afterCode next
  | .done out => ∃afterCode,ReentrantCallbacks.Effect view code store afterCode out.store ∧ OutcomeGuard view afterCode out

theorem acceptCall_guard {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (select : Selector) (state : State M)
    (held : ExecutableInv view code state.store) (stack : StackGuard memory view code state.store state.stack)
    (phase : CallPhase M Unit) (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (results : alloc.vec.Vec runtime.Value) (guard : CallTask memory view code state.store root signature phase) :
    ∃afterCode,ReentrantCallbacks.Effect view code state.store afterCode (acceptCall select state phase root results).store ∧
      StateGuard memory view afterCode (acceptCall select state phase root results) := by
  cases phase with
  | done answer =>
    obtain ⟨afterCode,effect,task⟩ := guard
    exact ⟨afterCode,effect,effect.invariant,⟨signature,task⟩,stack.extend effect⟩
  | pending exec after token address base identity args defaults =>
    obtain ⟨same,saved⟩ := guard
    subst after
    exact ⟨code,.refl held,held,trivial,⟨signature,saved⟩,stack⟩

theorem initialHost_guard {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (select : Selector) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (identity : U64) (args : Slice runtime.Value) :
    StateGuard memory view code (initialHost select store identity args) := ⟨held,trivial,trivial⟩
/-- A checked host invocation request prepares a fresh execution normally.
Its guard is derived from the current certified function/type tables, including
ordinary rejection of mismatched literal arguments. -/
theorem host_invoke_task {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (select : Selector) (state : State M) (held : ExecutableInv view code state.store)
    (host : HostState) (mode : state.mode=.host host) (index : Usize)
    (values : Slice PureCallbacks.Literal) (next : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values next)) (inside : index.val<state.store.funcs.length) :
    tick memory floats allocator select state ⦃out=>∃phase,InvokeTask memory view code state.store phase ∧
      out=.cont {state with
        mode:=.preparing phase,stack:=.host host next::state.stack,
        history:=state.history++[.invokeEnter ⟨state.store.id,index⟩ (OpenHostControl.literalValues values)]} ⦄ := by
  let function := state.store.funcs.val[index.val]
  have functionAt : state.store.funcs.val[index.val]?=some function := List.getElem?_eq_getElem inside
  have shape := held.shape.functions function (List.getElem_mem inside)
  let signature := state.store.types.val[function.signature.val]'shape.1
  have signatureAt : state.store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem shape.1
  unfold tick
  rw [mode]
  dsimp only
  rw [selected]
  simp only [if_pos inside,runtime.interp.Execution.new,bind_ok]
  obtain ⟨phase,actual,guard⟩ := WP.spec_imp_exists (prepare_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code _ state.store () held default Spec.empty_frame_wf ⟨state.store.id,index⟩
    function signature (OpenHostControl.literalValues values) (alloc.vec.Vec.new _) rfl
    ((PureCallbacks.Program.returned values).issued state.store) functionAt signatureAt)
  rw [actual,bind_ok]
  exact WP.spec.ret ⟨phase,guard.task memory held Spec.empty_frame_wf ⟨rfl,function,functionAt,signatureAt⟩,rfl⟩
end Exec.Theorems.OpenReentrantControl
