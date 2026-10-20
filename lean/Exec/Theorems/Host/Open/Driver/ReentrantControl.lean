import Exec.Interp.Host.OpenExecutionLoop
import Exec.Interp.Invocation.OpenInvoke
import Exec.Interp.Host.HostRecording
import Exec.Theorems.Host.Callbacks.CallbackActions
import Exec.Theorems.Host.Reentrant.CallbackInstantiationNoHost

/-! An executable combined driver with explicit suspended Wasm and host
continuations. The only callback dictionary used by a tick is inert; real host
calls are exposed by the proved resumable native adapters. Thus reentrancy
uses a stack, without a recursive Platform dictionary or a nesting-depth bound. -/
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

inductive Instruction where
  | returned (values : Slice PureCallbacks.Literal)
  | trapped
  | returnAction (segment : CallbackActions.Program)
  | jump (target : Nat)
  | branch (condition : Bool) (yes no : Nat)
  | action (segment : CallbackActions.Program) (next : Nat)
  | invoke (index : Usize) (arguments : Slice PureCallbacks.Literal) (next : Nat)
  | publish (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) (next : Nat)

abbrev Code := List Instruction
abbrev Selector := U64 → Slice runtime.Value → Code
abbrev HostStatus := core.result.Result Unit runtime.platform.HostError
abbrev Status := core.result.Result Unit runtime.ExecError
abbrev Reply (M : Type) := StoreCallbacks.Reply M

structure HostState where
  pc : Nat
  code : Code
  identity : U64
  arguments : Slice runtime.Value

inductive Continuation where
  | host (state : HostState) (next : Nat)
  | wasm (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
      (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)

inductive Observation where
  | hostEnter (address : Option runtime.FuncAddr) (identity : U64) (arguments : Slice runtime.Value)
  | hostExit (status : HostStatus) (values : Slice runtime.Value)
  | invokeEnter (address : runtime.FuncAddr) (arguments : Slice runtime.Value)
  | invokeExit (status : Status) (values : alloc.vec.Vec runtime.Value)
  | completedHost (depth : Nat) (events : List SpecExt.HostEvent)

inductive Mode (M : Type) where
  | host (state : HostState)
  | preparing (phase : InvokePhase M Unit)
  | wasm (exec : runtime.interp.Execution) (status : Status) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
  | hostReturn (status : HostStatus) (values : Slice runtime.Value)
  | invokeReturn (answer : InvokeAnswer M Unit)

structure State (M : Type) where
  store : runtime.store.Store M
  mode : Mode M
  stack : List Continuation
  history : List Observation

inductive Outcome (M : Type) where
  | host (answer : Reply M) (history : List Observation)
  | invocation (answer : InvokeAnswer M Unit) (history : List Observation)

/-- The inert hook is never used by resumable native call/step preparation.
Its interrupt behavior is the continuing policy used by this concrete driver. -/
def inert {M : Type} (memory : runtime.platform.MemoryBuffer M) : runtime.platform.Platform Unit M :=
  PureCallbacks.platform memory (fun _ _=>.trapped)

def invocationDepth : List Continuation → Nat
  | [] => 0
  | .host _ _::tail => invocationDepth tail+1
  | .wasm _ _ _ _ _::tail => invocationDepth tail

/-- A native pending phase pushes the caller continuation before selecting any
host code. Its entry store and immutable arguments are directly observable. -/
def acceptCall {M : Type} (select : Selector) (state : State M) (phase : CallPhase M Unit)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) : State M :=
  match phase with
  | .done answer => {state with store:=answer.2.2.1,mode:=.wasm answer.2.1 answer.1 root results}
  | .pending exec store _ address base identity args defaults =>
    {store,mode:=.host ⟨0,select identity args.slice,identity,args.slice⟩,
      stack:=.wasm exec address base root results :: state.stack,
      history:=state.history++[.hostEnter (some address) identity args.slice]}

/-- Compilation-backed publication is atomic only for modules without a start
function. Such a publication cannot hide a nested host or Wasm computation. -/
def publish {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits) : Result (HostStatus × runtime.store.Store M) := do
  let compiled ← runtime.compiler.compile_with allocator bytes profile limits
  match compiled with
  | .Err _ => .ok (.Err .Trap,store)
  | .Ok module =>
    if module.module.env.start=none then do
      let answer ← runtime.store.instantiate.Store.instantiate_with memory (inert memory) floats allocator store module (Slice.new _) ()
      match answer.1 with
      | .Ok _ => .ok (.Ok (),answer.2.1)
      | .Err _ => .ok (.Err .Trap,answer.2.1)
    else .ok (.Err .Trap,store)

/-- One executable combined tick. A nested invocation uses a new execution;
its completion resumes host control. A host reply resumes the captured native
continuation with the current committed store and the actual dynamic checker. -/
def tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (state : State M) : Result (ControlFlow (State M) (Outcome M)) := do
  match state.mode with
  | .host host =>
    match host.code[host.pc]? with
    | none => .ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _)})
    | some .trapped => .ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _)})
    | some (.returned values) => .ok (.cont {state with mode:=.hostReturn (.Ok ()) (OpenHostControl.literalValues values)})
    | some (.jump target) => .ok (.cont {state with mode:=.host {host with pc:=target}})
    | some (.branch condition yes no) => .ok (.cont {state with mode:=.host {host with pc:=if condition then yes else no}})
    | some (.returnAction segment) =>
      let answer ← segment.run memory allocator state.store
      .ok (.cont {state with store:=answer.2.1,mode:=.hostReturn answer.1 answer.2.2})
    | some (.action segment next) =>
      let answer ← segment.run memory allocator state.store
      match answer.1 with
      | .Ok () => .ok (.cont {state with store:=answer.2.1,mode:=.host {host with pc:=next}})
      | .Err error => .ok (.cont {state with store:=answer.2.1,mode:=.hostReturn (.Err error) answer.2.2})
    | some (.publish bytes profile limits next) =>
      let (status,after) ← publish memory floats allocator state.store bytes profile limits
      match status with
      | .Ok () => .ok (.cont {state with store:=after,mode:=.host {host with pc:=next}})
      | .Err error => .ok (.cont {state with store:=after,mode:=.hostReturn (.Err error) (Slice.new _)})
    | some (.invoke index values next) =>
      if index.val<state.store.funcs.length then
        let exec ← runtime.interp.Execution.new
        let args := OpenHostControl.literalValues values
        let address := (⟨state.store.id,index⟩ : runtime.FuncAddr)
        let phase ← prepareInvoke memory (inert memory) floats allocator exec state.store () address args (alloc.vec.Vec.new _)
        .ok (.cont {state with mode:=.preparing phase,stack:=.host host next :: state.stack,
                                history:=state.history++[.invokeEnter address args]})
      else .ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _)})
  | .preparing phase =>
    match phase with
    | .done answer => .ok (.cont {state with store:=answer.2.2.1,mode:=.invokeReturn answer})
    | .waiting callPhase root results => .ok (.cont (acceptCall select state callPhase root results))
  | .wasm exec status root results =>
    let phase ← prepareLoop memory (inert memory) floats allocator (exec,state.store,(),status)
    match phase with
    | .finished finished =>
      let answer ← readback memory allocator root results finished
      .ok (.cont {state with store:=answer.2.2.1,mode:=.invokeReturn answer})
    | .executing callPhase => .ok (.cont (acceptCall select state callPhase root results))
  | .hostReturn status values =>
    let observed := state.history++[.hostExit status values]
    match state.stack with
    | [] => .ok (.done (.host (status,state.store,values) observed))
    | .wasm exec address base root results::tail =>
      let (result,finished) ← hostResume memory exec state.store address base ⟨values⟩ status
      let events := hostCallEvents address (result,finished,state.store,())
      .ok (.cont {state with mode:=.wasm finished result root results,stack:=tail,
                                history:=observed++[.completedHost (invocationDepth tail) events]})
    | .host _ _::_ => .ok (.done (.host (.Err .Trap,state.store,Slice.new _) observed))
  | .invokeReturn answer =>
    let observed := state.history++[.invokeExit answer.1 answer.2.2.2.2]
    match state.stack with
    | [] => .ok (.done (.invocation answer observed))
    | .host host next::tail =>
      match answer.1 with
      | .Ok () => .ok (.cont {state with mode:=.host {host with pc:=next},stack:=tail,history:=observed})
      | .Err _ => .ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _),stack:=tail,history:=observed})
    | .wasm _ _ _ _ _::_ => .ok (.done (.host (.Err .Trap,state.store,Slice.new _) observed))

def run {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (state : State M) : Result (Outcome M) :=
  loop (tick memory floats allocator select) state

def initialHost {M : Type} (select : Selector) (store : runtime.store.Store M)
    (identity : U64) (args : Slice runtime.Value) : State M :=
  ⟨store,.host ⟨0,select identity args,identity,args⟩,[],[.hostEnter none identity args]⟩

/-- A synchronous callback implemented by the combined resumable driver.
There is no callback-normality premise and no recursion through its dictionary. -/
def platform {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) : runtime.platform.Platform Unit M where
  MemoryBufferInst:=memory
  interrupt token:=.ok (.Continue,token)
  call_host token store identity args _:=do
    let outcome ← run memory floats allocator select (initialHost select store identity args)
    match outcome with
    | .host (status,after,values) _ => .ok (status,token,after,values)
    | .invocation answer _ => .ok (.Err .Trap,token,answer.2.2.1,Slice.new _)

/-- A genuine host-local loop in the combined implementation. The pending call
and store remain present in every actual continuing tick. -/
theorem host_loop_diverges {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (identity : U64) (args : Slice runtime.Value) :
    run memory floats allocator (fun _ _=>[.jump 0])
      (initialHost (fun _ _=>[.jump 0]) store identity args)=.div := by
  apply loop_diverges_of_stream (tick memory floats allocator (fun _ _=>[.jump 0]))
    (fun _=>initialHost (fun _ _=>[.jump 0]) store identity args)
  intro n
  simp [tick,initialHost]

/-- The synchronous Platform method is connected to that same productive loop,
not to an inferred Wasm execution or an assumed callback-normality law. -/
theorem looping_platform_diverges {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (identity : U64) (args defaults : Slice runtime.Value) :
    (platform memory floats allocator (fun _ _=>[.jump 0])).call_host () store identity args defaults=.div := by
  simp only [platform,host_loop_diverges,bind_div]

/-- Root host returns retain the expanded history, including the initial
pending call and the exit. The ordinary platform wrapper erases this history. -/
theorem literal_return {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (identity : U64) (args : Slice runtime.Value)
    (values : Slice PureCallbacks.Literal) :
    run memory floats allocator (fun _ _=>[.returned values])
      (initialHost (fun _ _=>[.returned values]) store identity args)=
      .ok (.host (.Ok (),store,OpenHostControl.literalValues values)
        [.hostEnter none identity args,.hostExit (.Ok ()) (OpenHostControl.literalValues values)]) := by
  unfold run
  rw [loop.eq_def]
  simp only [tick,initialHost,List.getElem?_cons_zero,bind_ok]
  rw [loop.eq_def]
  simp only [tick,List.nil_append,List.cons_append,List.append_nil,bind_ok]
end Exec.Theorems.OpenReentrantControl
