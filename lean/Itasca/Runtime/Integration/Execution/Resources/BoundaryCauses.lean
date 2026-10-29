import Itasca.Runtime.Interp.Machine.Frames.FrameDepth
import Itasca.Runtime.Integration.Execution.Resources.FailureErrors
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Both direct and selected indirect calls explain exhaustion by decoded
source FRAME_ nesting at the actual failure site. -/
theorem CumulativeFailure.frame_depth
    {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState} {sourceStore : _root_.store}
    (stack : Machine.FrameStackRel store sourceStore exec source.frames)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .CallStack)) :
    store.limits.max_frames.val ≤ Spec.frameDepth (SourceMachine.decode source) := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · obtain ⟨target,offset,pc,address,base,function,ii,fi,callee,calleeCode,
        fetch,resolved,found,defined,hi,hc,baseEq,pcEq,cause⟩ := direct.concrete
      change store.limits.max_frames.val ≤ (exec.frames.set index {raw with pc:=pc}).length at cause
      simpa only [alloc.vec.Vec.set_length, stack.depth] using cause
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,
        fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      change store.limits.max_frames.val ≤ (exec.frames.set index {raw with pc:=pc}).length at cause
      simpa only [alloc.vec.Vec.set_length, stack.depth] using cause

/-- A termination result retains the exact interrupt decision, including calls. -/
theorem CumulativeFailure.interrupted {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : SourceMachine.AState}
    (failure : CumulativeFailure allocator hooks exec store platform source .Terminated) :
    ∃ after, hooks.interrupt platform = .ok (.Terminate,after) := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,decision⟩ | rejected
  · cases kind
  · exact decision
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · obtain ⟨target,offset,pc,address,base,function,ii,fi,callee,calleeCode,
        fetch,resolved,found,defined,hi,hc,baseEq,pcEq,cause⟩ := direct.concrete
      exact cause
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,
        fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      exact cause
end Itasca.Runtime.Integration
