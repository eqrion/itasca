import Exec.Interp.Machines.Slice.SliceNumeric
import Exec.Interp.Machines.Slice.SliceOrdinary
import Exec.Interp.Machines.Slice.SliceTerminal
import Exec.Interp.Relations.HeadCoverage

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_ready_slice {M P F A : Type}
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
    (point : StructuredFramePoint raw f compiled functions targets next output)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (result : Abs.InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (stack : FrameStackRel store exec (f :: rest)) (ready : ReadySource f) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, f :: rest, []⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    have labels : f.labels = [] := by simpa only [ReadySource, source] using ready
    have same : { f with code := [], labels := [] } = f := by rw [← source, ← labels]
    simpa only [same] using step_function_end_outcome memory hooks floats allocator exec store platform index raw inst compiled
      functions targets next output s ambient f rest last hf hi hc (by simpa only [same] using typed)
      (by simpa only [same] using slice) slots (by simpa only [same] using point) binding program
      (by simpa only [same] using stack) expected (by simpa only [same] using result)
  | cons op after =>
    have same : { f with code := op :: after } = f := by rw [← source]
    have nextTyped : Abs.ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ := by simpa only [same] using typed
    have nextSlice : Abs.SliceState ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ := by simpa only [same] using slice
    have nextResult : Abs.InvocationResult expected ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ := by simpa only [same] using result
    have nextStack : FrameStackRel store exec ({ f with code := op :: after } :: rest) := by simpa only [same] using stack
    have nextPoint : StructuredFramePoint raw { f with code := op :: after } compiled functions targets next output := by simpa only [same] using point
    have head := structured_head_coverage point (slice.active f (by simp)) ready op after source
    cases head with
    | numeric operation =>
      simpa only [same] using step_numeric_outcome memory hooks floats allocator exec store platform index raw inst compiled
        functions targets next output s ambient f rest operation after last hf hi hc program binding nextTyped nextSlice
        nextStack slots nextPoint expected nextResult
    | ordinary operation =>
      apply WP.spec_mono (step_opcode_advance memory hooks floats allocator exec store platform index raw inst compiled
        functions targets next output s ambient f rest operation after last hf hi hc program binding nextTyped nextSlice
        nextStack slots nextPoint expected nextResult)
      intro out effect
      obtain ⟨success, sameStore, advance⟩ := effect
      refine ⟨sameStore, ?_⟩
      simpa only [success, same] using advance
    | loop bt body =>
      apply WP.spec_mono (step_loop_advance memory hooks floats allocator interrupts exec store platform index raw inst compiled
        functions targets next output s ambient f rest bt body after last hf hi hc program binding nextTyped nextSlice
        nextStack slots nextPoint expected nextResult)
      intro out effect
      obtain ⟨sameStore, transition⟩ := effect
      refine ⟨sameStore, ?_⟩
      rcases transition with ⟨success, advance⟩ | ⟨terminated, hook⟩
      · simpa only [success, same] using advance
      · simp only [terminated]
        exact Or.inr (Or.inl ⟨rfl, out.2.2.2, hook⟩)
    | call functionIndex =>
      simpa only [same] using step_call_outcome memory hooks floats allocator allocation interrupts view code exec store platform
        index raw inst compiled functions targets next output s ambient f rest functionIndex after decoded compiledFunctions
        last hf hi hc nextTyped nextSlice binding slots program nextPoint nextStack expected nextResult
    | return_ =>
      simpa only [same] using step_return_outcome memory hooks floats allocator exec store platform index raw inst compiled
        functions targets next output s ambient f rest after last hf hi hc nextTyped nextSlice slots nextPoint binding program
        nextStack expected nextResult
    | unreachable =>
      simpa only [same] using step_unreachable_outcome memory hooks floats allocator exec store platform index raw inst compiled
        functions targets next output s ambient f rest after last hf hi hc nextTyped nextPoint program binding slots
        nextStack nextSlice expected nextResult

end Exec.Interp
