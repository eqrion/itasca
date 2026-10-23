import Exec.Interp.Core.OrdinaryExecution
import Exec.Interp.Core.Outcome
import Exec.Interp.Core.StructuredNormalization
import Exec.Interp.Relations.ControlPoint
import Exec.Spec.Extend
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem step_skip_core_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (platform : P) (frameIndex : Usize) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : CoreForwardSkip (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  obtain ⟨target,forward,fetched,retained⟩ := point
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target last frameFound found codeFound (program.fetched_bound _ fetched) fetched)
  intro out effect
  obtain ⟨success,exactState,storeSame,platformSame⟩ := effect
  apply CoreOutcome.unchanged_success storeSame success
  refine ⟨target.val,false,_,?_,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward retained.code.current.entry_bound⟩,fun _ h => h,rfl,fun _ h => h⟩
  exact machine.ordinary view code ambient f f rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
    (by rw [exactState]; exact slots) ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState])
    (by rw [exactState]; exact .refl _ _) machine.typed machine.core
end Exec.Interp
