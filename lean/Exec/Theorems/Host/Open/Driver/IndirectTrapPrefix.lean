import Exec.Theorems.Host.Open.Driver.EmptyIndirect
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A pending native host request executes the selected trapping instruction
and resumes its real Wasm continuation in three combined ticks. -/
theorem prepared_trap_prefix {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec ready : runtime.interp.Execution)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (identity : U64)
    (active : exec.frames.len>0#usize)
    (prepared : prepareStep memory (inert memory) floats allocator exec store ()=
      .ok (.pending ready store () address 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)))
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (tail : List Continuation) (history : List Observation) :
    let finished := {ready with host_results:=alloc.vec.Vec.new runtime.Value}
    let events := hostCallEvents address ((.Err (.Trap .Host) : Status),finished,store,())
    ContinuingTrace (tick memory floats allocator (fun _ _=>[.trapped])) 3
      ⟨store,.wasm exec (.Ok ()) root results,tail,history⟩
      ⟨store,.wasm finished (.Err (.Trap .Host)) root results,tail,
        history++[.hostEnter (some address) identity (Slice.new _),.hostExit (.Err .Trap) (Slice.new _),
          .completedHost (invocationDepth tail) events]⟩ := by
  let first : State M := ⟨store,.wasm exec (.Ok ()) root results,tail,history⟩
  let second : State M := ⟨store,.host ⟨0,[.trapped],identity,Slice.new _⟩,
    .wasm ready address 0#usize root results::tail,history++[.hostEnter (some address) identity (Slice.new _)]⟩
  let third : State M := {second with mode:=.hostReturn (.Err .Trap) (Slice.new _)}
  have tickFirst : tick memory floats allocator (fun _ _=>[.trapped]) first=.ok (.cont second) := by
    simp only [tick,first,prepareLoop,if_pos active,core.result.Result.is_ok,bind_ok,ite_true,prepared]
    rfl
  have tickSecond : tick memory floats allocator (fun _ _=>[.trapped]) second=.ok (.cont third) := by
    simp [tick,second,third]
  have tickThird : tick memory floats allocator (fun _ _=>[.trapped]) third=.ok (.cont
      ⟨store,.wasm {ready with host_results:=alloc.vec.Vec.new runtime.Value} (.Err (.Trap .Host)) root results,tail,
        history++[.hostEnter (some address) identity (Slice.new _),.hostExit (.Err .Trap) (Slice.new _),
          .completedHost (invocationDepth tail) (hostCallEvents address ((.Err (.Trap .Host) : Status),
            {ready with host_results:=alloc.vec.Vec.new runtime.Value},store,()))]⟩) := by
    simp [tick,third,second,hostResume,hostCallEvents,alloc.vec.Vec.new,List.append_assoc]
    rfl
  exact .next tickFirst (.next tickSecond (.next tickThird (.nil _)))
theorem empty_indirect_trap_prefix {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (frameIndex : Usize) (frame : runtime.interp.Frame) (entry index : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst)
    (position : U32) (reference : U64) (address : Usize) (function : runtime.store.FuncInst)
    (identity : U64) (signature : Itasca.types.FuncType)
    (last : frameIndex.val+1=exec.frames.length) (frameAt : exec.frames.val[frameIndex.val]?=some frame)
    (fetched : compiled.code.val[frame.pc.val]?=some (.CallIndirect entry index 0#u32))
    (pcBound : frame.pc.val<U32.max) (base : frame.base=0#usize)
    (instanceAt : store.instances.val[frame.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[frame.function.val]?=some compiled)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableMapped : inst.tables.val[table.val]?=some tableAddress)
    (tableAt : store.tables.val[tableAddress.index.val]?=some object)
    (input : UScalar.cast .U32 exec.slots.val[frame.base.val+index.val]! =position)
    (indexBound : frame.base.val+index.val<exec.slots.length)
    (signatureAt : inst.types.val[type.val]?=some function.signature)
    (selected : object.elements.val[position.val]?=some reference) (nonzero : reference≠0#u64)
    (encoded : (UScalar.cast .Usize reference).val=address.val+1)
    (functionAt : store.funcs.val[address.val]?=some function) (kind : function.code=.Host identity)
    (typeAt : store.types.val[function.signature.val]?=some signature)
    (params : signature.params.val=[]) (results : signature.results.val=[])
    (scratch : exec.host_args=alloc.vec.Vec.new runtime.Value)
    (root : runtime.FuncAddr) (returned : alloc.vec.Vec runtime.Value)
    (tail : List Continuation) (history : List Observation) :
    ∃next : U32,next.val=frame.pc.val+1 ∧
      ContinuingTrace (tick memory floats allocator (fun _ _=>[.trapped])) 3
        ⟨store,.wasm exec (.Ok ()) root returned,tail,history⟩
        ⟨store,.wasm {exec with
          frames:=exec.frames.set frameIndex {frame with pc:=next}
          host_results:=alloc.vec.Vec.new runtime.Value} (.Err (.Trap .Host)) root returned,tail,
          history++[.hostEnter (some ⟨store.id,address⟩) identity (Slice.new _),.hostExit (.Err .Trap) (Slice.new _),
            .completedHost (invocationDepth tail) [.call address.val [] none]]⟩ := by
  obtain ⟨next,nextEq,prepared⟩ := prepare_empty_indirect memory floats allocator allocation available exec store frameIndex frame
    entry index inst compiled table type tableAddress object position reference address function identity signature last frameAt fetched pcBound base
    instanceAt compiledAt pairAt tableMapped tableAt input indexBound signatureAt selected nonzero encoded functionAt kind typeAt params results scratch
  have active : exec.frames.len>0#usize := by scalar_tac
  have trace := prepared_trap_prefix memory floats allocator exec
    {exec with frames:=exec.frames.set frameIndex {frame with pc:=next}} store ⟨store.id,address⟩ identity active prepared root returned tail history
  exact ⟨next,nextEq,by simpa [hostCallEvents,scratch] using trace⟩

end Exec.Theorems.OpenReentrantControl
