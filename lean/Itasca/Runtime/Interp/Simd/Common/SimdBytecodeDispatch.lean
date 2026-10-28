import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdConstructor
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem dispatch_simd_of_view {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (instruction : runtime.bytecode.Instr) (op dst a entry : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry))) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base instruction = (do
      let (result,next,storeNext) ← runtime.interp.execute_simd memory floats exec store inst function base op dst a entry
      Result.ok (result,next,storeNext,platform)) := by
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,Option.some.injEq,reduceCtorEq,Prod.mk.injEq] at view
  all_goals first | contradiction | obtain ⟨rfl,rfl,rfl,rfl⟩ := view
  all_goals simp only [runtime.interp.dispatch,runtime.interp.dispatch_simd,runtime.interp.simd_operands,bind_ok,uncurry_apply_pair]

theorem step_simd_of_view {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (op dst a entry : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some inst)
    (hc : inst.module.functions.val[frame.function.val]? = some code)
    (hop : code.code.val[frame.pc.val]? = some instruction)
    (pcBound : frame.pc.val < U32.max)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry)))
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P → Prop)
    (handler : ∀ next : U32, next.val = frame.pc.val + 1 →
      runtime.interp.execute_simd memory floats
        {exec with frames := exec.frames.set index {frame with pc := next}}
        store frame.instance frame.function frame.base op dst a entry
        ⦃ out => post (out.1,out.2.1,out.2.2,platform) ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ post ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index frame inst code instruction
    last hf hi hc hop pcBound post
  intro next nextValue
  rw [dispatch_simd_of_view memory hooks floats allocator _ store platform index frame.instance frame.function frame.base
    instruction op dst a entry view]
  obtain ⟨⟨result,execution,storeNext⟩,returned,property⟩ := WP.spec_imp_exists (handler next nextValue)
  simpa only [returned,bind_ok,uncurry_apply_pair,WP.spec_ok] using property
end Itasca.Runtime.Interp
