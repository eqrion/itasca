import Exec.Interp.Host.OpenCall
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std Result
def prepareIndirect
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (exec : _root_.Exec.runtime.interp.Execution)
  (store : _root_.Exec.runtime.store.Store M) (platform : P) (inst : Std.Usize)
  (function : Std.Usize) (base : Std.Usize) (entry : Std.U32) (index : Std.U32)
  (callee : Std.U32) :
  Result (CallPhase M P)
  := do
  let i ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.store.ModuleInst) store.instances inst
  let cf ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.bytecode.CompiledFunction) i.module.functions
      function
  let i1 ← lift (UScalar.cast .Usize entry)
  let (table, ty) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Std.U32 ×
      Std.U32)) cf.indirect i1
  let i2 ← lift (UScalar.cast .Usize table)
  let ta ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.TableAddr) i.tables i2
  let i3 ← lift (UScalar.cast .Usize index)
  let i4 ← base + i3
  let i5 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U64)
      exec.slots i4
  let i6 ← lift (UScalar.cast .U32 i5)
  let i7 ← lift (UScalar.cast .Usize i6)
  let t ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.store.TableInst) store.tables ta.index
  let i8 := alloc.vec.Vec.len t.elements
  if i7 >= i8
  then
    let ee ←
      core.convert.IntoFrom.into runtime.ExecError.Insts.CoreConvertFromTrap
        runtime.Trap.TableOutOfBounds
    ok (.done (core.result.Result.Err ee, exec, store, platform))
  else
    let reference ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U64)
        t.elements i7
    if reference = 0#u64
    then
      let ee ←
        core.convert.IntoFrom.into runtime.ExecError.Insts.CoreConvertFromTrap
          runtime.Trap.UninitializedElement
      ok (.done (core.result.Result.Err ee, exec, store, platform))
    else
      let i9 ← lift (UScalar.cast .Usize reference)
      let f ← i9 - 1#usize
      let f1 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          _root_.Exec.runtime.store.FuncInst) store.funcs f
      let i10 ← lift (UScalar.cast .Usize ty)
      let i11 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
          i.types i10
      if f1.signature != i11
      then
        let ee ←
          core.convert.IntoFrom.into
            runtime.ExecError.Insts.CoreConvertFromTrap
            runtime.Trap.IndirectCallTypeMismatch
        ok (.done (core.result.Result.Err ee, exec, store, platform))
      else
        let i12 ← lift (UScalar.cast .Usize callee)
        let i13 ← base + i12
        prepareCall platformMemoryBufferInst platformPlatformInst
            platformFloatOpsInst platformAllocInst exec store platform
            { store := store.id, index := f } i13


def prepareDirect
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (exec : _root_.Exec.runtime.interp.Execution)
  (store : _root_.Exec.runtime.store.Store M) (platform : P) (inst : Std.Usize)
  (base : Std.Usize) (func : Std.U32) (callee : Std.U32) :
  Result (CallPhase M P)
  := do
  let i ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.store.ModuleInst) store.instances inst
  let i1 ← lift (UScalar.cast .Usize func)
  let addr ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      _root_.Exec.runtime.FuncAddr) i.funcs i1
  let i2 ← lift (UScalar.cast .Usize callee)
  let i3 ← base + i2
  prepareCall platformMemoryBufferInst platformPlatformInst
      platformFloatOpsInst platformAllocInst exec store platform addr i3


theorem erase_direct {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst base : Usize) (func callee : U32) :
    (do let phase ← prepareDirect memory hooks floats allocator exec store platform inst base func callee
        resume memory hooks phase)=
      runtime.interp.execute_call memory hooks floats allocator exec store platform inst base func callee := by
  simp only [prepareDirect,runtime.interp.execute_call,Std.bind_assoc,erase]
  repeat' first | rfl | (congr 1; funext x) |
    (cases x <;> simp_all only [Std.uncurry,Std.bind_assoc,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]) |
    (split <;> simp_all only [Std.bind_assoc,bind_ok])
  all_goals exact erase memory hooks floats allocator exec store platform _ _

theorem erase_indirect {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst function base : Usize) (entry index callee : U32) :
    (do let phase ← prepareIndirect memory hooks floats allocator exec store platform inst function base entry index callee
        resume memory hooks phase)=
      runtime.interp.execute_call_indirect memory hooks floats allocator exec store platform inst function base entry index callee := by
  simp only [prepareIndirect,runtime.interp.execute_call_indirect,Std.bind_assoc,erase,resume,bind_ok]
  repeat' first | rfl | (congr 1; funext x) |
    (cases x <;> simp_all only [Std.uncurry,Std.bind_assoc,bind_ok,resume,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]) |
    (split <;> simp_all only [Std.bind_assoc,bind_ok,resume,erase])
  all_goals exact erase memory hooks floats allocator exec store platform _ _

end Exec.Interp.OpenCall
