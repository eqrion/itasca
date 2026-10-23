import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Theorems.Composition.Cumulative.CumulativeBulkMutation
import Exec.Theorems.Composition.Stateful.StatefulDropStep
import Exec.Interp.StructuredMachine.JumpExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp
theorem StatefulDropEffect.cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before after : runtime.store.Store M} (effect : StatefulDropEffect before after)
    (certified : CertifiedCumulativeStore view code before) : CumulativeStoreMutation view code before after := by
  cases effect with
  | data address issued => exact data_drop_cumulative_mutation certified (List.getElem?_eq_getElem issued)
  | element address issued => exact element_drop_cumulative_mutation certified (List.getElem?_eq_getElem issued)

theorem stateful_drop_execution {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction) (isDrop : statefulIsDrop op=true)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Cumulative.FramePoint (decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Cumulative.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (certified : CertifiedCumulativeStore view code store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CumulativeStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_drop_point_step memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
    ambient f rest after op isDrop last frameFound found codeFound program.fetchBound moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=op.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact CumulativeStepOutcome.unchanged_success certified sameStore success ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨success,samePlatform,effect,metadata,pc,pcNext,exactState,represented,retained,transition⟩ := result
    have mutation := effect.cumulative_mutation certified
    apply CumulativeStepOutcome.success mutation success
    exact Cumulative.ordinary_step view code ambient {f with code:=op.source::after} {f with code:=after} rest expected raw.pc.val false
      machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
      (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition

end Exec.Theorems
