import Exec.Interp.Machines.Slice.SliceOutcome
import Exec.Interp.Control.StructuredCall
import Exec.Interp.Calls.ReturnStack
import Exec.Interp.Relations.EpilogueStack
import Exec.Interp.Control.StructuredUnreachable
import Exec.Interp.Relations.OrdinaryFetch

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_call_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (index : U32) (after : List instr)
    (decoded : s = Store.decodeStore view code store)
    (compiledFunctions : CompiledFunctions code store)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some caller)
    (hc : caller.module.functions.val[raw.function.val]? = some compiled)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (binding : FrameBinding store exec raw f)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (point : StructuredFramePoint raw { f with code := .CALL (.mk_uN index.val) :: after }
      compiled functions targets next output)
    (relation : FrameStackRel store exec ({ f with code := .CALL (.mk_uN index.val) :: after } :: rest))
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ out ⦄ := by
  apply WP.spec_mono (step_call_structured memory hooks floats allocator allocation interrupts view code exec store platform
    frameIndex raw caller compiled functions targets next output s ambient f rest index after decoded compiledFunctions
    last hf hi hc typed slice binding slots program point relation)
  intro out effect
  obtain ⟨sameStore, advanced, failure⟩ := effect
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    cases u
    obtain ⟨pc, frames, position, stack, nextTyped, nextSlice, simulation, ready, preserved, bounds, references⟩ := advanced status
    exact ⟨⟨s, ambient, frames, []⟩, pc.val, false,
      ⟨nextTyped, nextSlice, preserved expected result, stack, ready.cursor_at stack position⟩,
      rfl, rfl, simulation, bounds, references⟩
  | Err error => exact Or.inr (Or.inr ⟨frameIndex, raw, caller, compiled, last, hf, hi, hc, failure error status⟩)

theorem step_return_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .RETURN :: after }
      compiled functions targets next output)
    (binding : FrameBinding store exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (relation : FrameStackRel store exec ({ f with code := .RETURN :: after } :: rest))
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ out ⦄ := by
  apply WP.spec_mono (step_return_stack memory hooks floats allocator exec store platform index raw inst compiled functions
    targets next output s ambient f rest after last hf hi hc typed slice slots point binding program relation)
  intro out effect
  obtain ⟨success, sameStore, samePlatform, transition⟩ := effect
  refine ⟨sameStore, ?_⟩
  simp only [success]
  rcases transition with skip | returned
  · obtain ⟨stack, ready, target, exactState, decrease⟩ := skip
    have position : (out.2.1.frames.val.getLast?).map (fun raw => raw.pc) = some target := by
      rw [exactState, frames_set_last exec index _ last]
      simp
    exact ⟨⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩, target.val, false,
      ⟨typed, slice, result, stack, ready.cursor_at position⟩,
      rfl, rfl, Or.inl ⟨rfl, decrease⟩, (fun _ h => h), fun _ h => h⟩
  · obtain ⟨results, stack, represented, nextTyped, nextSlice, simulation, ready, preserved, bounds, references⟩ := returned
    exact SliceAdvance.ready nextTyped nextSlice (preserved expected result) stack ready (by cases rest <;> rfl) (by cases rest <;> rfl) simulation bounds references

theorem step_function_end_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := [], labels := [] }
      compiled functions targets next output)
    (binding : FrameBinding store exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (relation : FrameStackRel store exec ({ f with code := [], labels := [] } :: rest))
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ out ⦄ := by
  apply WP.spec_mono (step_function_end_stack memory hooks floats allocator exec store platform index raw inst compiled functions
    targets next output s ambient f rest  last hf hi hc typed slice slots point binding program relation)
  intro out effect
  obtain ⟨success, sameStore, samePlatform, transition⟩ := effect
  refine ⟨sameStore, ?_⟩
  simp only [success]
  rcases transition with skip | returned
  · obtain ⟨stack, ready, target, exactState, decrease⟩ := skip
    have position : (out.2.1.frames.val.getLast?).map (fun raw => raw.pc) = some target := by
      rw [exactState, frames_set_last exec index _ last]
      simp
    exact ⟨⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩, target.val, false,
      ⟨typed, slice, result, stack, ready.cursor_at position⟩,
      rfl, rfl, Or.inl ⟨rfl, decrease⟩, (fun _ h => h), fun _ h => h⟩
  · obtain ⟨stack, represented, nextTyped, nextSlice, simulation, ready, preserved, bounds, references⟩ := returned
    exact SliceAdvance.ready nextTyped nextSlice (preserved expected result) stack ready (by cases rest <;> rfl) (by cases rest <;> rfl) simulation bounds references

theorem step_unreachable_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩)
    (point : StructuredFramePoint raw { f with code := .UNREACHABLE :: after } compiled functions targets next output)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (slots : FrameSlots exec raw f)
    (stack : FrameStackRel store exec ({ f with code := .UNREACHABLE :: after } :: rest))
    (slice : Abs.SliceState ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩)
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SliceOutcome allocator hooks exec store platform expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩ out ⦄ := by
  obtain ⟨instruction, fetched, allowed⟩ := codeRel_ordinary_fetch point.code.current (by trivial)
  apply WP.spec_mono (step_unreachable_structured memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output s ambient f rest after last hf hi hc (program.fetched_bound _ fetched) typed point)
  intro out effect
  obtain ⟨sameStore, samePlatform, pc, exactState, transition⟩ := effect
  refine ⟨sameStore, ?_⟩
  rcases transition with advanced | trapped
  · obtain ⟨success, continuation, simulation⟩ := advanced
    simp only [success]
    have nextStack : FrameStackRel store out.2.1 ({ f with code := .UNREACHABLE :: after } :: rest) := by
      rw [exactState]
      exact stack.skip raw index pc last hf binding slots program continuation
    have top : out.2.1.frames.val.getLast? = some { raw with pc := pc } := by
      rw [exactState, frames_set_last exec index _ last]
      simp
    exact SliceAdvance.ordinary program result top ⟨targets, next, output, .ready continuation⟩
      nextStack typed slice ⟨rfl, rfl, rfl, rfl⟩ simulation (fun _ h => h) (fun _ h => h)
  · obtain ⟨status, reductions⟩ := trapped
    simp only [status]
    exact Or.inl ⟨⟨.Unreachable, rfl, Or.inl rfl⟩, reductions⟩

end Exec.Interp
