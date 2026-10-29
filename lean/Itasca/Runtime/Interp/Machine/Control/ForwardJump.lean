import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.SourceMachine.Core.Typing

/-!
A retained forward jump is a source stutter with a strictly decreasing administrative measure. It preserves all slot words and mutable store data.

Main declarations: `step_forward_jump_flat`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- A retained forward jump is a source stutter with a strictly decreasing
administrative measure. It preserves all slot words and mutable store data. -/
theorem step_forward_jump_flat {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
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
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set index {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} f ∧
      FramePoint sourceStore {raw with pc := target} f compiled C targets next output ∧
      SourceMachine.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩ ∧
      ConcreteSim compiled.code.length raw.pc.val target.val false false
        ⟨sourceStore,ambient,f::rest,[]⟩ ⟨sourceStore,ambient,f::rest,[]⟩ ⦄ := by
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target
    last frameFound instanceFound codeFound pcBound fetched)
  intro out effect
  obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
  refine ⟨success,sameStore,samePlatform,exactState,?_,point,typed,?_⟩
  · simpa only [exactState,FrameSlots] using slots
  · exact Or.inl ⟨rfl,dispatch_measure_forward _ _ _ _ forward point.code.current.entry_bound⟩
end Itasca.Runtime.Interp.Machine
