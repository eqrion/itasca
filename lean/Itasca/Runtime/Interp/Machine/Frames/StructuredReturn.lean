import Itasca.Runtime.Interp.Machine.Frames.ReturnPoint
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Relations.ControlPoint

/-!
Complete RETURN execution from a structured certificate. The certificate supplies the result suffix and word coordinates; an administrative forward skip retains the same source state and decreases the dispatch potential.

Main declarations: `step_return_structured`. A direct consumer is `Interp.Machine.Frames.ReturnExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Complete RETURN execution from a structured certificate. The certificate
supplies the result suffix and word coordinates; an administrative forward skip
retains the same source state and decreases the dispatch potential. -/
theorem step_return_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ≤ exec.slots.length)
    (point : FramePoint s raw { f with code := .RETURN :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((∃ target : U32,
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        FramePoint s { raw with pc := target } { f with code := .RETURN :: after }
          compiled C targets next output ∧
        dispatchMeasure false compiled.code.length target.val
          ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ <
        dispatchMeasure false compiled.code.length raw.pc.val
          ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) ∨
      (∃ front results src count,
        f.vals = front ++ results ∧ results.map SourceMachine.valueType = f.resultTypes ∧
        src = Compiler.slots ((f.locals ++ front).map Compiler.valueType) ∧
        count = Compiler.slots (results.map Compiler.valueType) ∧
        ValuesAt exec.slots.val (raw.base.val + src) results ∧
        raw.base.val + src + count ≤ exec.slots.length ∧
        ReturnEffect exec out.2.1 raw.base.val src count ∧
        ValuesAt out.2.1.slots.val raw.base.val results ∧
        SourceMachine.ATyped (returnedState s ambient rest results) ∧
        SourceMachine.NextSim ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩
          (returnedState s ambient rest results))) ⦄ := by
  have current := point.code.current
  rw [point.locals] at current
  rcases code_rel_return_values f.locals f.vals current with skip | actual
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    refine ⟨effect.1, effect.2.2.1, effect.2.2.2, Or.inl ⟨target, effect.2.1, ?_, ?_⟩⟩
    · exact ⟨point.bindings,point.locals,point.labels, ⟨by simpa only [point.locals] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    · exact dispatch_measure_forward _ _ _ _ forward continuation.entry_bound
  · obtain ⟨front, results, src, count, split, types, source, width, fetched⟩ := actual
    have bounds : raw.base.val + src.val + count.val ≤ exec.slots.length := by
      simpa only [split, source, width, List.map_append, Compiler.slots_append, Nat.add_assoc] using capacity
    have sourceBound : raw.base.val + src.val ≤ Usize.max := by scalar_tac
    have typed' : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩ := by
      simpa only [← split] using typed
    have next := return_next s ambient f rest after front results types
    have nextTyped := SourceMachine.instruction_preservation s ambient { f with vals := front ++ results }
      rest .RETURN after _ .ret typed' next
    have original : ValuesAt exec.slots.val (raw.base.val + src.val) results := by
      have words : WordsAt exec.slots.val raw.base.val
          (Compiler.encodeValues (f.locals ++ front) ++ Compiler.encodeValues results) := by
        simpa only [FrameSlots, ValuesAt, split, Compiler.encode_values_append, List.append_assoc] using slots
      simpa only [ValuesAt, Compiler.encode_values_length, source] using words.append_right
    apply WP.spec_mono (step_return_refines memory hooks floats allocator exec store platform
      index raw src count inst compiled last hf hi hc fetched pcBound s ambient f rest after front results
      typed' types (by simpa only [← split] using slots) source width bounds sourceBound)
    intro out effect
    obtain ⟨success, returned, represented, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, Or.inr ⟨front, results, src.val, count.val,
      split, types, source, width, original, bounds, returned, represented, nextTyped, ?_⟩⟩
    simpa only [← split] using simulation

end Itasca.Runtime.Interp.Machine
