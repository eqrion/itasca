import Exec.Interp.Control.SkipStack
import Exec.Interp.Control.StructuredNormalization

namespace Exec.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_forwardSkip_stack (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (stack : FrameStackRel store exec (f :: rest))
    (slots : FrameSlots exec raw f)
    (skip : ForwardSkip raw f compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ target : U32,
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        FrameStackRel store out.2.1 (f :: rest) ∧
        StructuredFramePoint { raw with pc := target } f compiled functions targets next output ∧
        ConcreteSim compiled.code.length raw.pc.val target.val false false
          ⟨s, ambient, f :: rest, []⟩ ⟨s, ambient, f :: rest, []⟩ ⦄ := by
  obtain ⟨target, forward, fetched, continuation⟩ := skip
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
    index raw inst compiled target last hf hi hc (program.fetched_bound _ fetched) fetched)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  exact ⟨success, sameStore, samePlatform, target, exactState,
    by rw [exactState]; exact stack.skip raw index target last hf binding slots program continuation,
    continuation, Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.code.current.entry_bound⟩⟩

theorem step_pendingJump_stack (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (stack : FrameStackRel store exec (f :: rest))
    (slots : FrameSlots exec raw f)
    (point : ControlPoint raw f compiled functions targets next output true) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ target : U32,
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        FrameStackRel store out.2.1 (f :: rest) ∧
        StructuredFramePoint { raw with pc := target } f compiled functions targets next output ∧
        ConcreteSim compiled.code.length raw.pc.val target.val true false
          ⟨s, ambient, f :: rest, []⟩ ⟨s, ambient, f :: rest, []⟩ ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc (program.fetched_bound _ fetched) fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    exact ⟨success, sameStore, samePlatform, target, exactState,
      by rw [exactState]; exact stack.skip raw index target last hf binding slots program continuation,
      continuation, Or.inl ⟨rfl, dispatchMeasure_jump _ _ _ _⟩⟩

end Exec.Interp
