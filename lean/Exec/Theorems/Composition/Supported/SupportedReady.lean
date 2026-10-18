import Exec.Theorems.Composition.Supported.SupportedDispatch
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.EpilogueExecution
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem step_ready_supported {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store) (free : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    apply WP.spec_mono (StructuredMachine.step_function_end_execution StructuredMachine.supportedReturnSemantics memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine))
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,fresh,simulation,ownership,ambientEq,bounded⟩ := effect
    apply SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status
    exact ⟨pc,false,nextSource,fresh,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have head := StructuredMachine.frame_head_coverage point ready op after source
    have result := step_head_supported language memory hooks floats allocator correct allocation interrupts view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small (by simpa only [same] using point) expected
      (by simpa only [same] using machine) shaped sourceSyntax bounds compiledFunctions functionTyping free (by simpa only [same] using owned)
    simpa only [same] using result
end Exec.Theorems
