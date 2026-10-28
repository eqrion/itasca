import Exec.Interp.Host.OpenExecuteCall
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

def completed {M P : Type} (run : Result (Answer M P)) : Result (CallPhase M P) := do
  let answer ← run
  .ok (.done answer)

/-- Call instructions expose a suspension; every other instruction executes
its existing extracted dispatcher. No opcode implementation is duplicated. -/
def prepareDispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex inst function base : Usize)
    (instruction : runtime.bytecode.Instr) : Result (CallPhase M P) :=
  match instruction with
  | .Call func callee => prepareDirect memory hooks floats allocator exec store platform inst base func callee
  | .CallIndirect entry index callee => prepareIndirect memory hooks floats allocator exec store platform inst function base entry index callee
  | _ => completed (runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base instruction)

def prepareStep
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (exec : _root_.Exec.runtime.interp.Execution)
  (store : _root_.Exec.runtime.store.Store M) (platform : P) :
  Result (CallPhase M P)
  := do
  let i := alloc.vec.Vec.len exec.frames
  let frame_index ← i - 1#usize
  let frame ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.interp.Frame) exec.frames frame_index
  let i1 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.store.ModuleInst) store.instances frame.instance
  let cf ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.bytecode.CompiledFunction) i1.module.functions
      frame.function
  let i2 ← lift (UScalar.cast .Usize frame.pc)
  let instruction ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.bytecode.Instr) cf.code i2
  let o ← lift (U32.checked_add frame.pc 1#u32)
  match o with
  | none =>
    .ok (.done (core.result.Result.Err runtime.ExecError.Internal, exec, store,
      platform))
  | some next =>
    let (f, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        _root_.Exec.runtime.interp.Frame) exec.frames frame_index
    let v := index_mut_back { f with pc := next }
    prepareDispatch platformMemoryBufferInst platformPlatformInst
      platformFloatOpsInst platformAllocInst { exec with frames := v } store
      platform frame_index frame.instance frame.function frame.base instruction

end Exec.Interp.OpenCall
