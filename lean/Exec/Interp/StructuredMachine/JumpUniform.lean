import Exec.Interp.StructuredMachine.PendingExecution
import Exec.Interp.StructuredMachine.JumpExecution
import Exec.Interp.StructuredMachine.UniformAdvance
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem step_forward_jump_uniform {owned : Abs.Ownership.Bounds → Abs.AState → Prop} {emission : FunctionEmission} {supported : Abs.AState → Prop}
    {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
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
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val false ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ⦄ := by
  apply WP.spec_mono (step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient f rest expected C targets next output target last frameFound found codeFound forward fetch slots point machine program)
  rintro out ⟨ok,same,platform,effect,fresh,simulation⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_forward fresh simulation forward (fun _ h => h) rfl (fun _ h => h)⟩

theorem step_pending_execution_uniform {owned : Abs.Ownership.Bounds → Abs.AState → Prop} {M P F A : Type} {emission : FunctionEmission} {supported : Abs.AState → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (platform : P) (frameIndex : Usize) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : ControlPoint emission (Store.decodeStore view code store) raw f compiled C targets next output true)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val true) :
runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val true ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ ⦄ := by
  apply WP.spec_mono (step_pending_execution memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨ok,same,platform,pc,fresh,simulation⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_pending fresh⟩

end Exec.Interp.StructuredMachine
