import Exec.Interp.StructuredMachine.Point
import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.ControlPoint
import Exec.Abs.Core.Typing
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- A retained forward jump is a source stutter with a strictly decreasing
administrative measure. It preserves all slot words and mutable store data. -/
theorem step_forward_jump_flat {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FramePoint sourceStore {raw with pc := target} f compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set index {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} f ∧
      FramePoint sourceStore {raw with pc := target} f compiled C targets next output ∧
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
end Itasca.Runtime.Interp.StructuredMachine
