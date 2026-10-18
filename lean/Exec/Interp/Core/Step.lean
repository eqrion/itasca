import Exec.Interp.Core.Ready
import Exec.Interp.Core.NormalizeExecution
import Exec.Interp.Core.NormalizeOutcome
import Exec.Interp.Core.SkipOutcome
import Exec.Interp.Core.PendingExecution
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem step_frame_core {M P F A : Type}
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
    (pending : Bool)
    (point : CoreControlPoint (Store.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply Or.inr
    apply WP.spec_mono (step_pending_core_execution memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact CoreOutcome.unchanged_success sameStore status ⟨pc.val,false,_,retained,simulation,fun _ h => h,rfl,fun _ h => h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      core_normalize_execution view code store exec raw index compiled C targets next output ambient f rest last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes C.FUNCS :=
      program.reposition raw.pc metadata
    rcases done with skip | ready
    · apply Or.inr
      apply WP.spec_mono (step_skip_core_outcome memory hooks floats allocator platform index view code exec store raw inst compiled
        ambient g rest C labels stop types hi represented last hf hc nextProgram skip expected retained)
      intro out outcome
      exact outcome.prepend_normalization chain machine.typed.typed
    · have nextModule : g.module = Store.decodeInstance store inst := metadata.module.trans moduleEq
      rcases step_ready_core memory hooks floats allocator allocation interrupts view laws code exec store platform index raw inst compiled
        C labels stop types ambient g rest compiledFunctions functionTyping last hf hi hc nextProgram represented nextModule small continuation expected retained ready with host | operation
      · exact Or.inl host
      · apply Or.inr
        apply WP.spec_mono operation
        intro out outcome
        exact outcome.prepend_normalization chain machine.typed.typed
end Exec.Interp
