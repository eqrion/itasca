import Exec.Theorems.Host.Open.Driver.MutualReentry
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- An independently specified host instruction enters the actual native
invocation adapter with empty arguments, preserving the outer continuation. -/
theorem empty_invoke_tick {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store) (select : Selector)
    (host : HostState) (next : Nat)
    (atInstruction : host.code[host.pc]?=some (.invoke w.wasmIndex (Slice.new _) next))
    (tail : List Continuation) (history : List Observation) :
    tick memory floats allocator select ⟨store,.host host,tail,history⟩=
      .ok (.cont ⟨store,.preparing (.waiting (.done (.Ok (),w.entry,store,())) w.address (alloc.vec.Vec.new _)),
        .host host next::tail,history++[.invokeEnter w.address (Slice.new _)]⟩) := by
  have inRange : w.wasmIndex.val<store.funcs.length := (List.getElem?_eq_some_iff.mp w.wasmAt).1
  have prepared := prepare_empty_invoke memory floats allocator allocation available store w.address rfl w.wasmFunction w.signature
    w.instanceIndex w.functionIndex w.inst w.compiled w.wasmAt w.signatureAt w.params w.results w.wasmKind w.instanceAt w.compiledAt
    w.paramSlots w.localSlots w.frameCapacity w.valueCapacity
  have literals : OpenHostControl.literalValues (Slice.new PureCallbacks.Literal)=Slice.new runtime.Value := by
    apply Slice.ext
    rfl
  simp only [emptyExecution,EmptyReentry.address] at prepared
  simp [tick,atInstruction,runtime.interp.Execution.new,literals,inRange,prepared,EmptyReentry.address,EmptyReentry.entry]

/-- The host reached by the wrapper is an actual suspension, for any selector. -/
theorem empty_host_tick {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store) (select : Selector)
    (tail : List Continuation) (history : List Observation) :
    tick memory floats allocator select ⟨store,.wasm w.entry (.Ok ()) w.address (alloc.vec.Vec.new _),tail,history⟩=
      .ok (.cont ⟨store,.host ⟨0,select w.identity (Slice.new _),w.identity,Slice.new _⟩,
        .wasm w.caller w.hostAddress 0#usize w.address (alloc.vec.Vec.new _)::tail,
        history++[.hostEnter (some w.hostAddress) w.identity (Slice.new _)]⟩) := by
  have called := prepare_empty_direct memory floats allocator allocation available store w.instanceIndex w.functionIndex w.inst w.compiled
    w.instanceAt w.compiledAt w.hostIndex w.hostAddress w.hostFunction w.identity w.hostSignature w.fetched w.addressAt w.hostAt
    w.hostKind w.hostSignatureAt w.hostParams w.hostResults
  change prepareStep memory (inert memory) floats allocator w.entry store ()=_ at called
  have active : w.entry.frames.len>0#usize := by simp [EmptyReentry.entry,emptyEntryExecution]
  simp only [tick,prepareLoop,if_pos active,core.result.Result.is_ok,bind_ok,ite_true,called]
  rfl

/-- This concrete host reenters Wasm, which calls a trapping host. The inner
trap is checked and propagated through both saved continuations; the outer
callback returns normally with a host trap and the expanded nested history. -/
theorem finite_reentry_trap {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store) (select : Selector)
    (outer : U64) (arguments : Slice runtime.Value) (next : Nat)
    (outerInstruction : (select outer arguments)[0]?=some (.invoke w.wasmIndex (Slice.new _) next))
    (innerInstruction : (select w.identity (Slice.new _))[0]?=some .trapped) :
    ∃history,run memory floats allocator select (initialHost select store outer arguments)=
      .ok (.host (.Err .Trap,store,Slice.new _) history) ∧
      NormalTrace (tick memory floats allocator select) 7 (initialHost select store outer arguments)
        (.host (.Err .Trap,store,Slice.new _) history) := by
  let host : HostState := ⟨0,select outer arguments,outer,arguments⟩
  let initial := initialHost select store outer arguments
  let second : State M := ⟨store,.preparing (.waiting (.done (.Ok (),w.entry,store,())) w.address (alloc.vec.Vec.new _)),
    [.host host next],initial.history++[.invokeEnter w.address (Slice.new _)]⟩
  let third : State M := {second with mode:=.wasm w.entry (.Ok ()) w.address (alloc.vec.Vec.new _)}
  let fourth : State M := ⟨store,.host ⟨0,select w.identity (Slice.new _),w.identity,Slice.new _⟩,
    [.wasm w.caller w.hostAddress 0#usize w.address (alloc.vec.Vec.new _),.host host next],
    third.history++[.hostEnter (some w.hostAddress) w.identity (Slice.new _)]⟩
  let fifth : State M := {fourth with mode:=.hostReturn (.Err .Trap) (Slice.new _)}
  let events := hostCallEvents w.hostAddress ((.Err (.Trap .Host) : Status),w.caller,store,())
  let sixth : State M := ⟨store,.wasm w.caller (.Err (.Trap .Host)) w.address (alloc.vec.Vec.new _),[.host host next],
    fifth.history++[.hostExit (.Err .Trap) (Slice.new _)]++[.completedHost 1 events]⟩
  let answer : InvokeAnswer M Unit := (.Err (.Trap .Host),w.caller,store,(),alloc.vec.Vec.new _)
  let seventh : State M := {sixth with mode:=.invokeReturn answer}
  let eighth : State M := ⟨store,.hostReturn (.Err .Trap) (Slice.new _),[],
    seventh.history++[.invokeExit (.Err (.Trap .Host)) (alloc.vec.Vec.new _)]⟩
  let observed := eighth.history++[.hostExit (.Err .Trap) (Slice.new _)]
  have firstTick : tick memory floats allocator select initial=.ok (.cont second) :=
    empty_invoke_tick memory floats allocator allocation available store w select host next outerInstruction [] initial.history
  have secondTick : tick memory floats allocator select second=.ok (.cont third) := by simp [tick,second,third,acceptCall]
  have thirdTick : tick memory floats allocator select third=.ok (.cont fourth) :=
    empty_host_tick memory floats allocator allocation available store w select [.host host next] third.history
  have fourthTick : tick memory floats allocator select fourth=.ok (.cont fifth) := by
    simp [tick,fourth,fifth,innerInstruction]
  have fifthTick : tick memory floats allocator select fifth=.ok (.cont sixth) := by
    simp [tick,fifth,fourth,sixth,hostResume,invocationDepth,events,hostCallEvents,alloc.vec.Vec.new,EmptyReentry.caller,emptyCallerExecution,emptyEntryExecution]
    rfl
  have sixthTick : tick memory floats allocator select sixth=.ok (.cont seventh) := by
    simp [tick,sixth,seventh,prepareLoop,core.result.Result.is_ok,finishExecution,readback,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,answer]
  have seventhTick : tick memory floats allocator select seventh=.ok (.cont eighth) := by
    simp [tick,seventh,eighth,sixth,answer]
  have eighthTick : tick memory floats allocator select eighth=.ok (.done (.host (.Err .Trap,store,Slice.new _) observed)) := by
    simp [tick,eighth,observed]
  have trace : NormalTrace (tick memory floats allocator select) 7 initial (.host (.Err .Trap,store,Slice.new _) observed) :=
    .next firstTick (.next secondTick (.next thirdTick (.next fourthTick (.next fifthTick (.next sixthTick (.next seventhTick (.done eighthTick)))))))
  exact ⟨observed,trace.result,trace⟩
end Exec.Theorems.OpenReentrantControl
