import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Interp.State.StatefulReadExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem stateful_read_execution {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Cumulative.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Cumulative.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (certified : CertifiedCumulativeStore view code store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CumulativeStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (Stateful.read_execution memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after op readOnly last frameFound found codeFound moduleEq slots point expected machine program)
  intro out result
  obtain ⟨sameStore,samePlatform,operation⟩ := result
  rcases operation with ⟨success,pc,g,fresh,simulation,owned,bound⟩ | ⟨error,trap⟩
  · exact CumulativeStepOutcome.unchanged_success certified sameStore success ⟨pc.val,false,_,fresh,simulation,owned,rfl,bound⟩
  · apply CumulativeStepOutcome.failure (by rw [sameStore];exact .refl certified) error (by rw [sameStore])
    exact Or.inl ⟨⟨.TableOutOfBounds,rfl,Or.inr (Or.inl rfl)⟩,trap⟩

end Exec.Theorems
