import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Interp.Machine.Stateful.ReadExecution
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem stateful_read_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (Stateful.read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after op readOnly last frameFound found codeFound moduleEq slots point expected machine program)
  intro out result
  obtain ⟨sameStore,samePlatform,operation⟩ := result
  rcases operation with ⟨success,pc,g,fresh,simulation,owned,bound⟩ | ⟨error,trap⟩
  · exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨pc.val,false,_,fresh,simulation,owned,rfl,bound⟩
  · apply SupportedStepOutcome.failure (by rw [sameStore];exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
    exact Or.inl ⟨⟨.TableOutOfBounds,rfl,Or.inr (Or.inl rfl)⟩,trap⟩

end Itasca.Runtime.Integration
