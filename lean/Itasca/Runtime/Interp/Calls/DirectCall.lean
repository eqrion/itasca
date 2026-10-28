import Itasca.Runtime.Interp.Calls.Call

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Resolving a direct call uses the caller's instance map and the emitted
callee-base offset. The callee's own instance is resolved by `call`. -/
theorem execute_call_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (callerIndex base : Usize) (func callee : U32)
    (caller : runtime.store.ModuleInst) (address : runtime.FuncAddr) (calleeBase : Usize)
    (hi : store.instances.val[callerIndex.val]? = some caller)
    (ha : caller.funcs.val[func.val]? = some address)
    (hb : calleeBase.val = base.val + callee.val)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (called : DivSpec cause (runtime.interp.call memory hooks floats allocator exec store platform
      address calleeBase) post) :
    DivSpec cause (runtime.interp.execute_call memory hooks floats allocator exec store platform
      callerIndex base func callee) post := by
  unfold runtime.interp.execute_call
  step with vec_index_given store.instances callerIndex caller hi as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given caller.funcs (UScalar.cast .Usize func) address
    (by simpa only [U32.cast_Usize_val_eq] using ha) as ⟨found, hfound⟩
  subst found
  step as ⟨actualBase, hbase⟩
  have heq : actualBase = calleeBase := by scalar_tac
  subst actualBase
  exact called

/-- Full instruction fetch advances the caller PC before entering a direct
callee, so successful return resumes after the CALL instruction. -/
theorem step_direct_call {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (callerCode : runtime.bytecode.CompiledFunction)
    (func callee : U32) (address : runtime.FuncAddr) (calleeBase : Usize)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some caller)
    (hc : caller.module.functions.val[frame.function.val]? = some callerCode)
    (hop : callerCode.code.val[frame.pc.val]? = some (.Call func callee))
    (pcBound : frame.pc.val < U32.max)
    (ha : caller.funcs.val[func.val]? = some address)
    (hb : calleeBase.val = frame.base.val + callee.val)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (called : ∀ next : U32, next.val = frame.pc.val + 1 →
      DivSpec cause (runtime.interp.call memory hooks floats allocator
        { exec with frames := exec.frames.set index { frame with pc := next } }
        store platform address calleeBase) post) :
    DivSpec cause (runtime.interp.step memory hooks floats allocator exec store platform) post := by
  apply step_fetch_div memory hooks floats allocator exec store platform index frame
    caller callerCode (.Call func callee) last hf hi hc hop pcBound cause post
  intro next hnext
  exact execute_call_effect memory hooks floats allocator _ store platform
    frame.instance frame.base func callee caller address calleeBase hi ha hb cause post (called next hnext)

end Itasca.Runtime.Interp
