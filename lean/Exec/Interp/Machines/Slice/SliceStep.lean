import Exec.Interp.Machines.Slice.SliceReady
import Exec.Interp.Control.NormalizeStack

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_slice_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (expected : List valtype)
    (decoded : s = Store.decodeStore view code store) (compiledFunctions : CompiledFunctions code store)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (pending : Bool)
    (point : ControlPoint raw f compiled functions targets next output pending)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (result : Abs.InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (stack : FrameStackRel store exec (f :: rest)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val pending
        ⟨s, ambient, f :: rest, []⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply WP.spec_mono (step_pendingJump_advance memory hooks floats allocator exec store platform index raw inst compiled
      functions targets next output s ambient f rest last hf hi hc program binding stack slots
      (.jump target fetched continuation) expected typed slice result)
    intro out effect
    obtain ⟨success, sameStore, advance⟩ := effect
    exact ⟨sameStore, by simpa only [success] using advance⟩
  | ready point =>
    obtain ⟨count, g, labels, stop, types, chain, bound, represented, continuation, nextTyped, nextSlice,
      nextStack, metadata, done⟩ := normalize_stack store exec raw index compiled functions targets next output
        s ambient f rest last hf binding program typed slice stack slots point
    have top : exec.frames.val.getLast? = some raw := by
      rw [List.getLast?_eq_getElem?]
      have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
      rw [position]
      exact hf
    have nextProgram : FrameProgram store raw compiled (g.locals.map Code.valueType) g.resultTypes functions :=
      program.reposition raw.pc metadata
    have nextBinding := (nextStack.top raw top).binding
    have nextResult := metadata.result s ambient rest expected result
    rcases done with skip | ready
    · apply WP.spec_mono (step_forwardSkip_advance memory hooks floats allocator exec store platform index raw inst compiled
        functions labels stop types s ambient g rest last hf hi hc nextProgram nextBinding nextStack represented
        skip expected nextTyped nextSlice nextResult)
      intro out effect
      obtain ⟨success, sameStore, advance⟩ := effect
      exact ⟨sameStore, by simpa only [success] using advance.prepend_normalization chain typed⟩
    · apply WP.spec_mono (step_ready_slice memory hooks floats allocator allocation interrupts view code exec store platform
        index raw inst compiled functions labels stop types s ambient g rest expected decoded compiledFunctions last hf hi hc
        nextProgram nextBinding represented continuation nextTyped nextSlice nextResult nextStack ready)
      intro out outcome
      exact outcome.prepend_normalization chain typed

end Exec.Interp
