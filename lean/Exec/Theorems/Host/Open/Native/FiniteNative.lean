import Exec.Theorems.Host.Open.Driver.ReentryContracts
import Exec.Interp.Invocation.OpenInvokeIndependent
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

theorem platform_trapping_instruction {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (select : Selector)
    (store : runtime.store.Store M) (identity : U64) (args defaults : Slice runtime.Value)
    (selected : (select identity args)[0]?=some .trapped) :
    (platform memory floats allocator select).call_host () store identity args defaults=
      .ok (.Err .Trap,(),store,Slice.new _) := by
  unfold platform run
  dsimp only
  rw [loop.eq_def]
  simp only [tick,initialHost,selected,bind_ok]
  rw [loop.eq_def]
  simp [tick]

/-- The finite wrapper's native synchronous invocation reaches the same host
trap as the explicit combined driver. The nested callback is the actual driver
Platform method, with its termination derived from its selected instruction. -/
theorem finite_reentry_native_invoke {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (store : runtime.store.Store M) (w : EmptyReentry store) (select : Selector)
    (innerInstruction : (select w.identity (Slice.new _))[0]?=some .trapped) :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator
      (emptyExecution 0#usize) store () w.address (Slice.new _) (alloc.vec.Vec.new _)=
      .ok (.Err (.Trap .Host),w.caller,store,(),alloc.vec.Vec.new _) := by
  let hooks := platform memory floats allocator select
  have interrupts : ∀p,hooks.interrupt p=(inert memory).interrupt p := by intro p; rfl
  have prepared := prepare_empty_invoke memory floats allocator allocation available store w.address rfl w.wasmFunction w.signature
    w.instanceIndex w.functionIndex w.inst w.compiled w.wasmAt w.signatureAt w.params w.results w.wasmKind w.instanceAt w.compiledAt
    w.paramSlots w.localSlots w.frameCapacity w.valueCapacity
  have called := prepare_empty_direct memory floats allocator allocation available store w.instanceIndex w.functionIndex w.inst w.compiled
    w.instanceAt w.compiledAt w.hostIndex w.hostAddress w.hostFunction w.identity w.hostSignature w.fetched w.addressAt w.hostAt
    w.hostKind w.hostSignatureAt w.hostParams w.hostResults
  change prepareStep memory (inert memory) floats allocator w.entry store ()=_ at called
  have active : w.entry.frames.len>0#usize := by simp [EmptyReentry.entry,emptyEntryExecution]
  have nativeStep : executionBody memory hooks floats allocator (w.entry,store,(),(.Ok () : Status))=
      .ok (.cont (w.caller,store,(),(.Err (.Trap .Host) : Status))) := by
    rw [←erase_loop_body,prepareLoop_independent memory hooks (inert memory) floats allocator _ interrupts]
    simp only [prepareLoop,if_pos active,core.result.Result.is_ok,bind_ok,ite_true,called,resumeLoop,resume]
    have trapping := platform_trapping_instruction memory floats allocator select store w.identity (Slice.new _) (Slice.new _) innerInstruction
    change hooks.call_host () store w.identity (Slice.new _) (Slice.new _)=_ at trapping
    simp only [show (alloc.vec.Vec.new runtime.Value).slice=Slice.new _ from rfl,trapping,bind_ok,hostResume]
    simp [Std.uncurry,hostResume,EmptyReentry.caller,emptyCallerExecution,emptyEntryExecution] <;> rfl
  have stopped : executionBody memory hooks floats allocator (w.caller,store,(),(.Err (.Trap .Host) : Status))=
      .ok (.done (finishExecution (w.caller,store,(),(.Err (.Trap .Host) : Status)))) := by
    rw [←erase_loop_body]
    simp [prepareLoop,core.result.Result.is_ok,resumeLoop]
  have nativeLoop : runtime.interp.invoke_with_loop1 memory hooks floats allocator w.entry store () (.Ok ())=
      .ok (finishExecution (w.caller,store,(),(.Err (.Trap .Host) : Status))) := by
    change loop (executionBody memory hooks floats allocator) (w.entry,store,(),(.Ok () : Status))=_
    exact (NormalTrace.next nativeStep (.done stopped)).result
  change prepareInvoke memory (inert memory) floats allocator (emptyExecution 0#usize) store () w.address (Slice.new _) (alloc.vec.Vec.new _)=
    .ok (.waiting (.done (.Ok (),w.entry,store,())) w.address (alloc.vec.Vec.new _)) at prepared
  change runtime.interp.invoke_with memory hooks floats allocator (emptyExecution 0#usize) store () w.address (Slice.new _) (alloc.vec.Vec.new _)=_
  rw [←erase_invoke,prepareInvoke_independent memory hooks (inert memory) floats allocator _ _ _ _ _ _ interrupts,prepared]
  simp only [eraseInvoke,resume,bind_ok,afterInitialCall,Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
  rw [nativeLoop]
  simp [Std.uncurry,readback,finishExecution,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Exec.Theorems.OpenReentrantControl
