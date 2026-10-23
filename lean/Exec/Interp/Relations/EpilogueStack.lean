import Exec.Interp.Calls.ReturnReferenceBounds
import Exec.Interp.Calls.ReturnSlice
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Calls.FunctionEnd
import Exec.Interp.Control.SkipStack
import Exec.Interp.Relations.Capacity

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Falling off the source body executes the checked epilogue and preserves
the full frame stack. Forward skips retain the same source configuration. -/
theorem step_function_end_stack {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
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
    (relation : FrameStackRel store exec ({ f with code := [], labels := [] } :: rest)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((FrameStackRel store out.2.1 ({ f with code := [], labels := [] } :: rest) ∧
        ReadyTop store out.2.1 { f with code := [], labels := [] } ∧
        ∃ target : U32,
          out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
          dispatchMeasure false compiled.code.length target.val
            ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ <
          dispatchMeasure false compiled.code.length raw.pc.val
            ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) ∨
      (FrameStackRel store out.2.1 (returnedState s ambient rest f.vals).frames ∧
        ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
        Abs.ATyped (returnedState s ambient rest f.vals) ∧
        Abs.SliceState (returnedState s ambient rest f.vals) ∧
        Abs.NextSim ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩
          (returnedState s ambient rest f.vals) ∧
        ReadyState store out.2.1 (returnedState s ambient rest f.vals) ∧
        (∀ expected, Abs.InvocationResult expected
            ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ →
          Abs.InvocationResult expected (returnedState s ambient rest f.vals)) ∧
        (∀ bound, Abs.CodeBound bound ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ →
          Abs.CodeBound bound (returnedState s ambient rest f.vals)) ∧
        (∀ bound, Abs.StateReferencesBound bound ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ →
          Abs.StateReferencesBound bound (returnedState s ambient rest f.vals)))) ⦄ := by
  rcases structured_function_end program point with skip | terminal
  · obtain ⟨target, forward, fetched, targetPoint⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc (program.fetched_bound _ fetched) fetched)
    intro out result
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := result
    refine ⟨success, sameStore, samePlatform, Or.inl ⟨?_, ?_, target, exactState, dispatchMeasure_forward _ _ _ _ forward targetPoint.code.current.entry_bound⟩⟩
    · rw [exactState]
      exact relation.skip raw index target last hf binding slots program targetPoint
    · refine ⟨{ raw with pc := target }, compiled, functions, targets, next, output, ?_, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩, targetPoint⟩
      rw [exactState, frames_set_last exec index _ last]
      simp
  · obtain ⟨count, fetched, localSlots, width, pcBound⟩ := terminal
    obtain ⟨types, nextTyped, simulation⟩ := frame_end_source s ambient f rest typed
    have codeTypes : f.vals.map Code.valueType = f.resultTypes := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types
    have actualWidth : count.val = Code.slots (f.vals.map Code.valueType) := by rw [codeTypes]; exact width
    have capacity := slots.capacity binding
    have bounds : raw.base.val + compiled.local_slots.val + count.val ≤ exec.slots.length := by
      simpa only [List.map_append, Code.slots_append, localSlots, actualWidth, Nat.add_assoc] using capacity
    have original : ValuesAt exec.slots.val (raw.base.val + compiled.local_slots.val) f.vals := by
      simpa only [localSlots] using slots.operands
    apply WP.spec_mono (step_epilogue_refines memory hooks floats allocator exec store platform
      index raw compiled.local_slots count inst compiled last hf hi hc fetched pcBound
      s ambient { f with labels := [] } rest (Or.inl rfl) typed slots localSlots width capacity)
    intro out result
    obtain ⟨success, effect, represented, sameStore, samePlatform, preserved, next⟩ := result
    have top : exec.frames.val.getLast? = some raw := by
      rw [List.getLast?_eq_getElem?]
      have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
      rw [position]
      exact hf
    have complete := relation.return_complete s ambient raw top effect f.vals original codeTypes actualWidth bounds
      (fun caller member => typed.heights caller (by simp [member]))
    exact ⟨success, sameStore, samePlatform, Or.inr ⟨complete.1, represented, nextTyped,
      returnedState_slice slice f.vals, simulation, complete.2,
      function_end_invocation_result s ambient f rest typed types,
      (fun _ bounded => returnedState_codeBound bounded f.vals), fun bound bounded =>
        returnedState_referenceBound bounded (bounded.2 _ (List.mem_cons_self ..)).2⟩⟩

end Exec.Interp
