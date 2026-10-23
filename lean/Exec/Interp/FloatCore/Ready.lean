import Exec.Interp.Machines.FloatCore.FloatCoreHeadCoverage
import Exec.Interp.Numeric.Float.FloatScalarExecution
import Exec.Interp.FloatCore.HeadStep
import Exec.Interp.Machines.FloatCore.FloatCoreEpilogueExecutionOwned
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem step_ready_float_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (compiledFunctions : FloatCoreCompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FloatFramePoint (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : FloatCoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      FloatCoreOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels = [] := by simpa only [ReadySource,source] using ready
    have same : {f with code := [],labels := []} = f := by rw [←source,←labels]
    apply Or.inr
    have operation := step_function_end_float_core_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine)
    apply WP.spec_mono operation
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,machine,simulation,ownership,ambientEq,bounded⟩ := effect
    apply FloatCoreOutcome.unchanged_success sameStore status
    exact ⟨pc,false,nextSource,machine,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code := op::after} = f := by rw [←source]
    have head := float_core_head_coverage point ready op after source
    rcases head with base | ⟨scalar, rfl⟩
    · have operation := step_head_float_core_base memory hooks floats allocator allocation interrupts view laws code exec store platform index raw inst compiled
        C targets next output ambient f rest op after base compiledFunctions functionTyping last hf hi hc program slots moduleEq small
        (by simpa only [same] using point) expected (by simpa only [same] using machine)
      simpa only [same] using operation
    · apply Or.inr
      apply WP.spec_mono (step_scalar_float_execution memory hooks floats allocator correct exec store platform index raw inst compiled
        C targets next output view code ambient f rest scalar after last hf hi hc slots
        (by simpa only [same] using point) expected (by simpa only [same] using machine) program)
      intro out effect
      simpa only [same] using effect.2.2
end Exec.Interp
