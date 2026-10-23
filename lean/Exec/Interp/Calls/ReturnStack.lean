import Exec.Interp.Calls.ReturnReferenceBounds
import Exec.Interp.Calls.ReturnSlice
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Control.StructuredReturn
import Exec.Interp.Control.SkipStack
import Exec.Interp.Relations.Capacity

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A complete RETURN iteration preserves the whole frame relation, including
resumption of the immediate caller and all older suspended frames. -/
theorem step_return_stack {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
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
    (relation : FrameStackRel store exec ({ f with code := .RETURN :: after } :: rest)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((FrameStackRel store out.2.1 ({ f with code := .RETURN :: after } :: rest) ∧
        ReadyTop store out.2.1 { f with code := .RETURN :: after } ∧
        ∃ target : U32,
          out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
          dispatchMeasure false compiled.code.length target.val
            ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ <
          dispatchMeasure false compiled.code.length raw.pc.val
            ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) ∨
      (∃ results, FrameStackRel store out.2.1 (returnedState s ambient rest results).frames ∧
        ValuesAt out.2.1.slots.val raw.base.val results ∧
        Abs.ATyped (returnedState s ambient rest results) ∧
        Abs.SliceState (returnedState s ambient rest results) ∧
        Abs.NextSim ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩
          (returnedState s ambient rest results) ∧
        ReadyState store out.2.1 (returnedState s ambient rest results) ∧
        (∀ expected, Abs.InvocationResult expected
            ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ →
          Abs.InvocationResult expected (returnedState s ambient rest results)) ∧
        (∀ bound, Abs.CodeBound bound ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ →
          Abs.CodeBound bound (returnedState s ambient rest results)) ∧
        (∀ bound, Abs.StateReferencesBound bound ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ →
          Abs.StateReferencesBound bound (returnedState s ambient rest results)))) ⦄ := by
  have pcBound : raw.pc.val < U32.max := by
    rcases codeRel_return_values f.locals f.vals point.code.current with skip | actual
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      exact program.fetched_bound _ fetched
    · obtain ⟨front, results, src, count, split, types, source, width, fetched⟩ := actual
      exact program.fetched_bound _ fetched
  apply WP.spec_mono (step_return_structured memory hooks floats allocator exec store platform
    index raw inst compiled functions targets next output s ambient f rest after last hf hi hc pcBound
    typed slots (slots.capacity binding) point)
  intro out result
  obtain ⟨success, sameStore, samePlatform, transition⟩ := result
  refine ⟨success, sameStore, samePlatform, ?_⟩
  rcases transition with skip | returned
  · obtain ⟨target, exactState, targetPoint, decrease⟩ := skip
    refine Or.inl ⟨?_, ?_, target, exactState, decrease⟩
    · rw [exactState]
      exact relation.skip raw index target last hf binding slots program targetPoint
    · refine ⟨{ raw with pc := target }, compiled, functions, targets, next, output, ?_, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩, targetPoint⟩
      rw [exactState, frames_set_last exec index _ last]
      simp
  · obtain ⟨front, results, src, count, split, types, source, width, original, bounds,
      effect, represented, nextTyped, simulation⟩ := returned
    have top : exec.frames.val.getLast? = some raw := by
      rw [List.getLast?_eq_getElem?]
      have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
      rw [position]
      exact hf
    have complete := relation.return_complete s ambient raw top effect results original
      (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types)
      width bounds (fun caller member => typed.heights caller (by simp [member]))
    exact Or.inr ⟨results, complete.1, represented, nextTyped, returnedState_slice slice results, simulation,
      complete.2, return_invocation_result s ambient f rest after front results typed split types,
      (fun _ bounded => returnedState_codeBound bounded results), by
        intro bound bounded
        have values := (bounded.2 { f with code := .RETURN :: after } (by simp)).2
        change Abs.ValuesBound bound f.vals at values
        rw [split] at values
        exact returnedState_referenceBound bounded (Abs.valuesBound_append.mp values).2⟩

end Exec.Interp
