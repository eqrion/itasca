import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Core.Point
import Exec.Interp.Relations.ControlPoint
import Exec.Abs.Core.Typing
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A retained forward jump is a source stutter with a strictly decreasing
administrative measure. It preserves all slot words and mutable store data. -/
theorem step_float_forward_jump {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (target : U32)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (forward : raw.pc.val < target.val)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
    (slots : FrameSlots exec raw f)
    (point : FloatFramePoint sourceStore {raw with pc := target} f compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set index {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} f ∧
      FloatFramePoint sourceStore {raw with pc := target} f compiled C targets next output ∧
      Abs.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩ ∧
      ConcreteSim compiled.code.length raw.pc.val target.val false false
        ⟨sourceStore,ambient,f::rest,[]⟩ ⟨sourceStore,ambient,f::rest,[]⟩ ⦄ := by
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target
    last frameFound instanceFound codeFound pcBound fetched)
  intro out effect
  obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
  refine ⟨success,sameStore,samePlatform,exactState,?_,point,typed,?_⟩
  · simpa only [exactState,FrameSlots] using slots
  · exact Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward point.code.current.entry_bound⟩
end Exec.Interp
