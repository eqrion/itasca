import Exec.Interp.Host.OpenFetch
import Exec.Interp.Control.PendingJump
import Exec.Interp.Control.LoopHead
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

theorem prepare_jump_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (target : U32)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (pcBound : raw.pc.val<U32.max) (fetched : compiled.code.val[raw.pc.val]?=some (.Jump target)) :
    prepareStep memory hooks floats allocator exec store platform =
      .ok (.done (.Ok (),{exec with frames:=exec.frames.set index {raw with pc:=target}},store,platform)) := by
  have total := prepare_step_fetch memory hooks floats allocator exec store platform index raw inst compiled (.Jump target)
    last hf hi hc fetched pcBound
    (fun phase=>phase=.done (.Ok (),{exec with frames:=exec.frames.set index {raw with pc:=target}},store,platform)) (by
      intro pc hpc
      have valid : index.val<exec.frames.val.length := (List.getElem?_eq_some_iff.mp hf).1
      have lookup : (exec.frames.set index {raw with pc:=pc}).val[index.val]?=some {raw with pc:=pc} := by
        simp [alloc.vec.Vec.set_val_eq,valid]
      obtain ⟨out,actual,success,exactState,sameStore,samePlatform⟩ := WP.spec_imp_exists
        (dispatch_jump_exact memory hooks floats allocator {exec with frames:=exec.frames.set index {raw with pc:=pc}}
          store platform index raw.instance raw.function raw.base {raw with pc:=pc} target lookup)
      have frames : (exec.frames.set index {raw with pc:=pc}).set index {raw with pc:=target}=
          exec.frames.set index {raw with pc:=target} := by
        apply alloc.vec.Vec.ext
        simp only [alloc.vec.Vec.set_val_eq,List.set_set]
      simp only [frames] at exactState
      have outEq : out=(.Ok (),{exec with frames:=exec.frames.set index {raw with pc:=target}},store,platform) := by
        rcases out with ⟨status,after,afterStore,token⟩
        simp only [Prod.mk.injEq] at *
        exact ⟨success,exactState,sameStore,samePlatform⟩
      simp only [prepareDispatch,completed,actual,bind_ok]
      exact WP.spec.ret (congrArg CallPhase.done outEq))
  obtain ⟨phase,actual,rfl⟩ := WP.spec_imp_exists total
  exact actual

end Exec.Interp.OpenCall
