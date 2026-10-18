import Exec.Interp.Numeric.Integer.NumericStack
import Exec.Interp.Machines.Slice.SliceOutcome

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (stack : FrameStackRel store exec ({ f with code := op.source :: after } :: rest))
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := op.source :: after } compiled functions targets next output)
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ out ⦄ := by
  apply WP.spec_mono (step_numeric_advance memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output s ambient f rest op after last hf hi hc program binding typed slice stack slots point
    expected result)
  intro out effect
  obtain ⟨sameStore, transition⟩ := effect
  refine ⟨sameStore, ?_⟩
  rcases transition with ⟨success, advanced⟩ | ⟨trap, rejected, kind, source⟩
  · simpa only [success] using advanced
  · simp only [rejected]
    exact .inl ⟨⟨trap, rfl, .inr kind⟩, source⟩
end Exec.Interp
