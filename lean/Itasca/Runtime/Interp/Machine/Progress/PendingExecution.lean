import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Spec.Extend

/-!
Machine progress with a pending control continuation.

Main declarations: `step_pending_execution`. A direct consumer is `Integration.Execution.Dispatch.HostSite`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem step_pending_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (platform : P) (frameIndex : Usize) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : ControlPoint (Store.decodeStore view code store) raw f compiled C targets next output true)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val true) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, Execution view code store out.2.1 initial expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val true false initial initial ⦄ := by
  dsimp only
  cases point with
  | jump target fetched retained =>
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target last frameFound found codeFound (program.fetched_bound _ fetched) fetched)
    intro out effect
    obtain ⟨success,exactState,storeSame,platformSame⟩ := effect
    refine ⟨success,storeSame,platformSame,target,?_,Or.inl ⟨rfl,dispatch_measure_jump _ _ _ _⟩⟩
    exact machine.ordinary view code ambient f f rest expected raw.pc.val true (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
      (by rw [exactState]; exact slots) ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState])
      (by rw [exactState]; exact .refl _ _) machine.typed machine.core
end Itasca.Runtime.Interp.Machine
