import Exec.Interp.Core.HeadStep
import Exec.Interp.Machines.Core.CoreEpilogueExecutionOwned
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem step_ready_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (compiledFunctions : CoreCompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : CoreFramePoint (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels = [] := by simpa only [ReadySource,source] using ready
    have same : {f with code := [],labels := []} = f := by rw [←source,←labels]
    apply Or.inr
    have operation := step_function_end_core_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine)
    apply WP.spec_mono operation
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,machine,simulation,ownership,ambientEq,bounded⟩ := effect
    apply CoreOutcome.unchanged_success sameStore status
    exact ⟨pc,false,nextSource,machine,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code := op::after} = f := by rw [←source]
    have head := core_head_coverage point ready op after source
    have operation := step_head_core memory hooks floats allocator allocation interrupts view laws code exec store platform index raw inst compiled
      C targets next output ambient f rest op after head compiledFunctions functionTyping last hf hi hc program slots moduleEq small
      (by simpa only [same] using point) expected (by simpa only [same] using machine)
    simpa only [same] using operation
end Exec.Interp
