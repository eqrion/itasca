import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.Relations.ControlPoint
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem step_forward_jump {emission : FunctionEmission} {supported : Abs.AState → Prop}
    {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (expected : List valtype)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) (target : U32)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (forward : raw.pc.val<target.val) (fetch : compiled.code.val[raw.pc.val]?=some (.Jump target))
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) {raw with pc:=target} f compiled C targets next output)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
      out.2.1={exec with frames:=exec.frames.set index {raw with pc:=target}} ∧
      Execution emission supported view code store out.2.1 ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected target.val false ∧
      ConcreteSim compiled.code.length raw.pc.val target.val false false
        ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ⦄ := by
  have pcBound : raw.pc.val<U32.max := by
    have inside := (List.getElem?_eq_some_iff.mp fetch).1
    have bound := program.fetchBound
    omega
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target last frameFound found codeFound pcBound fetch)
  intro out effect
  obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
  refine ⟨success,sameStore,samePlatform,exactState,?_,?_⟩
  · apply Execution.ordinary view code ambient f f rest expected raw.pc.val false machine (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw index target last frameFound program (.ready point)
    · simpa only [exactState,FrameSlots] using slots
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · simp only [exactState]
    · simpa only [exactState] using SlotPrefix.refl raw.base.val exec.slots.val
    · exact machine.typed
    · exact machine.core
  · exact Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward point.code.current.entry_bound⟩
end Exec.Interp.StructuredMachine
