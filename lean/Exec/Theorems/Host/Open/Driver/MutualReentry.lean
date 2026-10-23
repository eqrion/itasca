import Exec.Theorems.Host.Open.Driver.EmptyDirect
import Exec.Theorems.Host.Open.Driver.EmptyInvoke
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Independent raw metadata and resource bounds for a Wasm wrapper which
immediately calls an empty-signature host. No invocation outcome is assumed. -/
structure EmptyReentry {M : Type} (store : runtime.store.Store M) where
  wasmIndex : Usize
  wasmFunction : runtime.store.FuncInst
  signature : Itasca.types.FuncType
  instanceIndex : Usize
  functionIndex : Usize
  inst : runtime.store.ModuleInst
  compiled : runtime.bytecode.CompiledFunction
  wasmAt : store.funcs.val[wasmIndex.val]?=some wasmFunction
  wasmKind : wasmFunction.code=.Wasm instanceIndex functionIndex
  signatureAt : store.types.val[wasmFunction.signature.val]?=some signature
  params : signature.params.val=[]
  results : signature.results.val=[]
  instanceAt : store.instances.val[instanceIndex.val]?=some inst
  compiledAt : inst.module.functions.val[functionIndex.val]?=some compiled
  paramSlots : compiled.param_slots=0#u32
  localSlots : compiled.local_slots=0#u32
  frameCapacity : 0<store.limits.max_frames.val
  valueCapacity : compiled.slot_count.val≤store.limits.max_values.val
  hostIndex : U32
  hostAddress : runtime.FuncAddr
  hostFunction : runtime.store.FuncInst
  identity : U64
  hostSignature : Itasca.types.FuncType
  fetched : compiled.code.val[0]?=some (.Call hostIndex 0#u32)
  addressAt : inst.funcs.val[hostIndex.val]?=some hostAddress
  hostAt : store.funcs.val[hostAddress.index.val]?=some hostFunction
  hostKind : hostFunction.code=.Host identity
  hostSignatureAt : store.types.val[hostFunction.signature.val]?=some hostSignature
  hostParams : hostSignature.params.val=[]
  hostResults : hostSignature.results.val=[]

def EmptyReentry.address {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) : runtime.FuncAddr :=
  ⟨store.id,w.wasmIndex⟩
def EmptyReentry.entry {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) : runtime.interp.Execution :=
  emptyEntryExecution store.id w.instanceIndex w.functionIndex w.compiled.slot_count
def EmptyReentry.caller {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) : runtime.interp.Execution :=
  emptyCallerExecution store.id w.instanceIndex w.functionIndex w.compiled.slot_count
def EmptyReentry.host {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) : HostState :=
  ⟨0,[.invoke w.wasmIndex (Slice.new _) 0],w.identity,Slice.new _⟩
def EmptyReentry.push {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) (tail : List Continuation) :=
  .wasm w.caller w.hostAddress 0#usize w.address (alloc.vec.Vec.new _) :: .host w.host 0 :: tail
def EmptyReentry.events {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store) : List Observation :=
  [.invokeEnter w.address (Slice.new _),.hostEnter (some w.hostAddress) w.identity (Slice.new _)]

/-- Three actual driver ticks complete a host-to-Wasm-to-host cycle, adding
both suspended continuations. Every fresh Wasm execution has just one frame. -/
theorem mutual_reentry_cycle {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) :
    let select : Selector := fun _ _=>w.host.code
    let first : State M := ⟨store,.host w.host,tail,history⟩
    let second : State M := ⟨store,.preparing (.waiting (.done (.Ok (),w.entry,store,())) w.address (alloc.vec.Vec.new _)),
      .host w.host 0::tail,history++[.invokeEnter w.address (Slice.new _)]⟩
    let third : State M := {second with mode:=.wasm w.entry (.Ok ()) w.address (alloc.vec.Vec.new _)}
    tick memory floats allocator select first=.ok (.cont second) ∧
    tick memory floats allocator select second=.ok (.cont third) ∧
    tick memory floats allocator select third=.ok (.cont ⟨store,.host w.host,w.push tail,history++w.events⟩) := by
  have inRange : w.wasmIndex.val<store.funcs.length := (List.getElem?_eq_some_iff.mp w.wasmAt).1
  have prepared := prepare_empty_invoke memory floats allocator allocation available store w.address rfl w.wasmFunction w.signature
    w.instanceIndex w.functionIndex w.inst w.compiled w.wasmAt w.signatureAt w.params w.results w.wasmKind w.instanceAt w.compiledAt
    w.paramSlots w.localSlots w.frameCapacity w.valueCapacity
  have called := prepare_empty_direct memory floats allocator allocation available store w.instanceIndex w.functionIndex w.inst w.compiled
    w.instanceAt w.compiledAt w.hostIndex w.hostAddress w.hostFunction w.identity w.hostSignature w.fetched w.addressAt w.hostAt
    w.hostKind w.hostSignatureAt w.hostParams w.hostResults
  have active : w.entry.frames.len>0#usize := by simp [EmptyReentry.entry,emptyEntryExecution]
  have literals : OpenHostControl.literalValues (Slice.new PureCallbacks.Literal)=Slice.new runtime.Value := by
    apply Slice.ext
    rfl
  dsimp only
  constructor
  · simp only [emptyExecution,EmptyReentry.address] at prepared
    simp [tick,EmptyReentry.host,runtime.interp.Execution.new,literals,inRange,
      prepared,EmptyReentry.address,EmptyReentry.entry]
  constructor
  · simp [tick,acceptCall]
  · simp only [tick,prepareLoop,if_pos active,core.result.Result.is_ok,bind_ok,ite_true]
    change prepareStep memory (inert memory) floats allocator w.entry store ()=_ at called
    rw [called]
    simp [bind_ok,acceptCall,EmptyReentry.caller,EmptyReentry.push,EmptyReentry.host,EmptyReentry.events,List.append_assoc]
    rfl

def EmptyReentry.stackAt {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store)
    (tail : List Continuation) : Nat → List Continuation
  | 0=>tail
  | n+1=>w.push (w.stackAt tail n)

def EmptyReentry.historyAt {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store)
    (history : List Observation) : Nat → List Observation
  | 0=>history
  | n+1=>w.historyAt history n++w.events

/-- The productive stream includes both native preparation ticks; no callback
activity is inferred merely from the result `.div`. -/
def EmptyReentry.states {M : Type} {store : runtime.store.Store M} (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) (n : Nat) : State M :=
  let stack:=w.stackAt tail (n/3)
  let observed:=w.historyAt history (n/3)
  if n%3=0 then ⟨store,.host w.host,stack,observed⟩
  else if n%3=1 then
    ⟨store,.preparing (.waiting (.done (.Ok (),w.entry,store,())) w.address (alloc.vec.Vec.new _)),
      .host w.host 0::stack,observed++[.invokeEnter w.address (Slice.new _)]⟩
  else
    ⟨store,.wasm w.entry (.Ok ()) w.address (alloc.vec.Vec.new _),
      .host w.host 0::stack,observed++[.invokeEnter w.address (Slice.new _)]⟩

theorem mutual_reentry_stream {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) :
    ∀n,tick memory floats allocator (fun _ _=>w.host.code) (w.states tail history n)=
      .ok (.cont (w.states tail history (n+1))) := by
  intro n
  have cycle := mutual_reentry_cycle memory floats allocator allocation available store w
    (w.stackAt tail (n/3)) (w.historyAt history (n/3))
  by_cases zero : n%3=0
  · have next : (n+1)%3=1 := by omega
    have quotient : (n+1)/3=n/3 := by omega
    simpa only [EmptyReentry.states,if_pos zero,if_neg (by omega : (n+1)%3≠0),if_pos next,quotient] using cycle.1
  · by_cases one : n%3=1
    · have next : (n+1)%3=2 := by omega
      have quotient : (n+1)/3=n/3 := by omega
      simpa only [EmptyReentry.states,if_neg zero,if_pos one,
        if_neg (by omega : (n+1)%3≠0),if_neg (by omega : (n+1)%3≠1),quotient] using cycle.2.1
    · have next : (n+1)%3=0 := by omega
      have quotient : (n+1)/3=n/3+1 := by omega
      simpa only [EmptyReentry.states,if_neg zero,if_neg one,if_pos next,quotient,
        EmptyReentry.stackAt,EmptyReentry.historyAt] using cycle.2.2

/-- Mutual host/Wasm nesting is unbounded even when each fresh native
execution uses a single Wasm frame. Every cycle retains its pending entries. -/
theorem mutual_reentry_diverges {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) :
    run memory floats allocator (fun _ _=>w.host.code) ⟨store,.host w.host,tail,history⟩=.div := by
  exact loop_diverges_of_stream (tick memory floats allocator (fun _ _=>w.host.code)) (w.states tail history)
    (mutual_reentry_stream memory floats allocator allocation available store w tail history)

theorem mutual_reentry_stack_unbounded {M : Type} (store : runtime.store.Store M) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) (n : Nat) :
    (w.states tail history (3*n)).stack.length=tail.length+2*n := by
  have count : ∀n,(w.stackAt tail n).length=tail.length+2*n := by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>simp only [EmptyReentry.stackAt,EmptyReentry.push,List.length_cons]; omega
  simpa [EmptyReentry.states] using count n

theorem mutual_reentry_store {M : Type} (store : runtime.store.Store M) (w : EmptyReentry store)
    (tail : List Continuation) (history : List Observation) (n : Nat) :
    (w.states tail history n).store=store := by
  simp only [EmptyReentry.states]
  split <;> try rfl
  split <;> rfl

end Exec.Theorems.OpenReentrantControl
