import Itasca.Runtime.Interp.Memory.MemoryLoadFootprint
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
 theorem step_load_footprint {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.memoryLoadInstruction op address address offset))
    (pcBound : raw.pc.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () → ∃ word, raw.base.val+address.val < exec.slots.length ∧
        out.2.1.slots.val = exec.slots.val.set (raw.base.val+address.val) word ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Code.memoryLoadInstruction op address address offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have actualValues : ValuesAt exec.slots.val raw.base.val ((f.locals++front) ++ [Abs.integerVal .I32 bits]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append] using addressSlot
  have handler := execute_load_footprint memory view laws {exec with frames := exec.frames.set index {raw with pc := pc}} store raw.instance raw.base op address offset inst memoryAddress object (f.locals++front) bits found mapped issued actualValues actualAddress bitsBound
  apply WP.spec_mono (dispatch_load memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address address offset handler)
  intro out effect success
  obtain ⟨word,bound,footprint⟩ := effect.1 success
  exact ⟨word,bound,footprint.1⟩
end Itasca.Runtime.Interp.MemoryDescriptor
