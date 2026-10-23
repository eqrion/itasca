import Exec.Interp.Host.OpenFetch
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

theorem prepare_direct_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (callerIndex base : Usize) (func callee : U32)
    (caller : runtime.store.ModuleInst) (address : runtime.FuncAddr) (calleeBase : Usize)
    (hi : store.instances.val[callerIndex.val]?=some caller)
    (ha : caller.funcs.val[func.val]?=some address) (hb : calleeBase.val=base.val+callee.val)
    (post : CallPhase M P → Prop)
    (called : prepareCall memory hooks floats allocator exec store platform address calleeBase ⦃post⦄) :
    prepareDirect memory hooks floats allocator exec store platform callerIndex base func callee ⦃post⦄ := by
  unfold prepareDirect
  step with vec_index_given store.instances callerIndex caller hi as ⟨found,same⟩
  subst found
  simp only [lift,bind_ok]
  step with vec_index_given caller.funcs (UScalar.cast .Usize func) address
    (by simpa only [U32.cast_Usize_val_eq] using ha) as ⟨found,same⟩
  subst found
  step as ⟨actualBase,hbase⟩
  have same : actualBase=calleeBase := by scalar_tac
  subst actualBase
  exact called

/-- Fetched direct calls expose the host suspension after the exact native
address resolution and caller PC update. -/
theorem prepare_step_direct_call {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (func callee : U32) (address : runtime.FuncAddr) (calleeBase : Usize)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some frame)
    (hi : store.instances.val[frame.instance.val]?=some caller)
    (hc : caller.module.functions.val[frame.function.val]?=some compiled)
    (fetched : compiled.code.val[frame.pc.val]?=some (.Call func callee)) (pcBound : frame.pc.val<U32.max)
    (addressAt : caller.funcs.val[func.val]?=some address) (baseOffset : calleeBase.val=frame.base.val+callee.val)
    (post : CallPhase M P → Prop)
    (called : ∀next : U32,next.val=frame.pc.val+1 →
      prepareCall memory hooks floats allocator {exec with frames:=exec.frames.set index {frame with pc:=next}}
        store platform address calleeBase ⦃post⦄) :
    prepareStep memory hooks floats allocator exec store platform ⦃post⦄ := by
  apply prepare_step_fetch memory hooks floats allocator exec store platform index frame caller compiled (.Call func callee)
    last hf hi hc fetched pcBound post
  intro next nextEq
  exact prepare_direct_effect memory hooks floats allocator _ store platform frame.instance frame.base func callee caller address calleeBase
    hi addressAt baseOffset post (called next nextEq)
end Exec.Interp.OpenCall
