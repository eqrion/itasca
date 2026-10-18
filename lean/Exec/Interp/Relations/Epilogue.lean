import Exec.Interp.Calls.ReturnRefinement
import Exec.Abs.Sim.Step
import Exec.Abs.Sim.Compose

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

def resultLabel (types : List valtype) : Abs.Label := ⟨types, types, [], 0, []⟩

/-- Falling off an unlabeled function body returns exactly its declared values,
with a generated FRAME reduction and preservation of caller typing. -/
theorem frame_end_source (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    f.vals.map Abs.valueType = f.resultTypes ∧
    Abs.ATyped (returnedState s ambient rest f.vals) ∧
    Abs.NextSim ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩
      (returnedState s ambient rest f.vals) := by
  have frameTyped : Abs.FrameTyped s { f with code := [], labels := [] } [] := by
    cases typed.frames with | cons h _ => exact h
  have values := Abs.frame_end_typed frameTyped
  have types := Abs.results_type_of_typed values
  have length : f.resultTypes.length = f.vals.length := (Spec.resultsTyped_length values).symm
  have step : Abs.astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ =
      .next (returnedState s ambient rest f.vals) := by
    cases rest <;> simp [Abs.astep, Abs.returnFrame, Abs.AFrame.arity, length, types, returnedState, Abs.advance]
  refine ⟨types, ?_, Abs.NextSim.single (Abs.typed_frame_end_simulation s ambient f rest _ typed step)⟩
  have preserved := Abs.return_values_preservation typed values
  cases rest <;> exact preserved

/-- The ordinary function epilogue fuses root-label completion and frame
completion. Both source transitions are proved from the generated typing rules. -/
theorem epilogue_source (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩) :
    f.vals.map Abs.valueType = f.resultTypes ∧
    Abs.ATyped (returnedState s ambient rest f.vals) ∧
    Abs.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
      (returnedState s ambient rest f.vals) := by
  rcases labels with empty | root
  · simpa only [← empty] using frame_end_source s ambient f rest (by simpa only [← empty] using typed)
  · have frameTyped : Abs.FrameTyped s { f with code := [], labels := [resultLabel f.resultTypes] } [] := by
      have frames := typed.frames
      cases frames with | cons h _ => simpa only [← root] using h
    have exited := Abs.label_exit_frame_preservation frameTyped
    have noLabels : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ :=
      Abs.active_frame_preservation typed exited rfl
    obtain ⟨types, nextTyped, returned⟩ := frame_end_source s ambient f rest noLabels
    have length : f.vals.length = f.resultTypes.length := by
      have h := congrArg List.length types
      simpa only [List.length_map] using h
    have step : Abs.astep ⟨s, ambient, { f with code := [], labels := [resultLabel f.resultTypes] } :: rest, []⟩ =
        .next ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ := by
      simp [Abs.astep, resultLabel, length, types, Abs.advance]
    have first := Abs.typed_label_end_simulation s ambient f rest (resultLabel f.resultTypes) [] _
      (by simpa only [← root] using typed) step
    refine ⟨types, nextTyped, ?_⟩
    simpa only [← root] using first.trans returned


/-- The actual epilogue Return copies the typed result vector and implements
root-label/frame completion, including zero results and an empty call stack. -/
theorem dispatch_epilogue_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Code.slots (f.locals.map Code.valueType))
    (width : count.val = Code.slots f.resultTypes)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.Return src count) ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.ATyped (returnedState s ambient rest f.vals) ∧
      Abs.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
        (returnedState s ambient rest f.vals) ⦄ := by
  obtain ⟨types, nextTyped, simulation⟩ := epilogue_source s ambient f rest labels typed
  have types' : f.vals.map Code.valueType = f.resultTypes := by
    have equal : Code.valueType = Abs.valueType := by
      funext value
      cases value with
      | REF_NULL ty => cases ty <;> rfl
      | _ => rfl
    rw [equal, types]
  have bounds : raw.base.val + src.val + count.val ≤ exec.slots.length := by
    simpa only [source, width, List.map_append, Code.slots_append, types', Nat.add_assoc] using capacity
  have sourceBound : raw.base.val + src.val ≤ Usize.max := by scalar_tac
  have represented : ValuesAt exec.slots.val (raw.base.val + src.val) f.vals := by
    simpa only [source] using ValuesAt.operands slots
  simp only [runtime.interp.dispatch]
  step with return_effect memory hooks floats allocator exec raw.base src count bounds sourceBound
    as ⟨result, next, success, effect⟩
  exact ⟨success, effect, effect.results represented (by rw [types', width]) bounds, nextTyped, simulation⟩

/-- Complete fetched epilogue iteration with exact frame removal. -/
theorem step_epilogue_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Return src count))
    (pcBound : raw.pc.val < U32.max)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Code.slots (f.locals.map Code.valueType))
    (width : count.val = Code.slots f.resultTypes)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) ≤ exec.slots.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.ATyped (returnedState s ambient rest f.vals) ∧
      Abs.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
        (returnedState s ambient rest f.vals) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.Return src count) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_epilogue_refines memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw src count s ambient f rest labels typed slots source width capacity)
  intro out effect
  exact ⟨effect.1, effect.2.1.before_fetch last, effect.2.2⟩

end Exec.Interp
