import Exec.Interp.Control.JumpTable
import Exec.Abs.BrTable
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem step_brTable_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (selector start len target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (labels : List labelidx) (fallback : labelidx) (front : List val)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled)
    (last : frameIndex.val+1 = exec.frames.length)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.JumpTable selector start len))
    (bound : value < 2^32) (tableLength : len.val = labels.length+1)
    (tableBound : start.val + labels.length ≤ U32.max)
    (targetLookup : compiled.jump_tables.val[start.val + Nat.min value labels.length]? = some target)
    (position : selector.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (typed : Abs.ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [Abs.integerVal .I32 value]}::rest,[]⟩)
    (slots : FrameSlots exec raw {f with vals := front ++ [Abs.integerVal .I32 value]}) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := target}} ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      FrameSlots out.2.1 {raw with pc := target} {f with code := .BR (Abs.BrTable.select labels fallback value)::after,vals := front} ∧
      Abs.ATyped ⟨s,ambient,{f with code := .BR (Abs.BrTable.select labels fallback value)::after,vals := front}::rest,[]⟩ ∧
      Abs.NextSim ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after,vals := front ++ [Abs.integerVal .I32 value]}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (Abs.BrTable.select labels fallback value)::after,vals := front}::rest,[]⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [Abs.integerVal .I32 value]) := by
    simpa only [FrameSlots,List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + selector.val) [value] := by
    simpa only [position,ValuesAt,Code.encodeValues,List.flatMap_cons,List.flatMap_nil,
      Abs.integerVal,Code.encodeValue,List.append_nil] using allValues.operands
  obtain ⟨nextTyped,simulation⟩ := Abs.BrTable.correct s ambient f rest after front value labels fallback bound typed
  apply WP.spec_mono (step_jumpTable_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled
    selector start len target value last frameLookup instanceLookup functionLookup pcBound fetched bound input (by omega)
    (by simpa only [tableLength,Nat.add_sub_cancel] using tableBound)
    (by simpa only [tableLength,Nat.add_sub_cancel] using targetLookup))
  rintro out ⟨success,exactState,sameStore,samePlatform⟩
  refine ⟨success,exactState,sameStore,samePlatform,?_,nextTyped,simulation⟩
  simpa only [exactState,FrameSlots] using allValues.locals
end Itasca.Runtime.Interp
