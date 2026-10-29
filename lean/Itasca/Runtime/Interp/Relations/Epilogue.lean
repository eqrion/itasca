import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.SourceMachine.Sim.Step
import Itasca.Runtime.SourceMachine.Sim.Compose

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

def resultLabel (types : List valtype) : SourceMachine.Label := ⟨types, types, [], 0, []⟩

/-- Falling off an unlabeled function body returns exactly its declared values,
with a generated FRAME reduction and preservation of caller typing. -/
theorem frame_end_source (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    f.vals.map SourceMachine.valueType = f.resultTypes ∧
    SourceMachine.ATyped (returnedState s ambient rest f.vals) ∧
    SourceMachine.NextSim ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩
      (returnedState s ambient rest f.vals) := by
  have frameTyped : SourceMachine.FrameTyped s { f with code := [], labels := [] } [] := by
    cases typed.frames with | cons h _ => exact h
  have values := SourceMachine.frame_end_typed frameTyped
  have types := SourceMachine.results_type_of_typed values
  have length : f.resultTypes.length = f.vals.length := (Spec.results_typed_length values).symm
  have step : SourceMachine.astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ =
      .next (returnedState s ambient rest f.vals) := by
    cases rest <;> simp [SourceMachine.astep, SourceMachine.returnFrame, SourceMachine.AFrame.arity, length, types, returnedState, SourceMachine.advance]
  refine ⟨types, ?_, SourceMachine.NextSim.single (SourceMachine.typed_frame_end_simulation s ambient f rest _ typed step)⟩
  have preserved := SourceMachine.return_values_preservation typed values
  cases rest <;> exact preserved

/-- The ordinary function epilogue fuses root-label completion and frame
completion. Both source transitions are proved from the generated typing rules. -/
theorem epilogue_source (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩) :
    f.vals.map SourceMachine.valueType = f.resultTypes ∧
    SourceMachine.ATyped (returnedState s ambient rest f.vals) ∧
    SourceMachine.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
      (returnedState s ambient rest f.vals) := by
  rcases labels with empty | root
  · simpa only [← empty] using frame_end_source s ambient f rest (by simpa only [← empty] using typed)
  · have frameTyped : SourceMachine.FrameTyped s { f with code := [], labels := [resultLabel f.resultTypes] } [] := by
      have frames := typed.frames
      cases frames with | cons h _ => simpa only [← root] using h
    have exited := SourceMachine.label_exit_frame_preservation frameTyped
    have noLabels : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ :=
      SourceMachine.active_frame_preservation typed exited rfl
    obtain ⟨types, nextTyped, returned⟩ := frame_end_source s ambient f rest noLabels
    have length : f.vals.length = f.resultTypes.length := by
      have h := congrArg List.length types
      simpa only [List.length_map] using h
    have step : SourceMachine.astep ⟨s, ambient, { f with code := [], labels := [resultLabel f.resultTypes] } :: rest, []⟩ =
        .next ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ := by
      simp [SourceMachine.astep, resultLabel, length, types, SourceMachine.advance]
    have first := SourceMachine.typed_label_end_simulation s ambient f rest (resultLabel f.resultTypes) [] _
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
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Compiler.slots (f.locals.map Compiler.valueType))
    (width : count.val = Compiler.slots f.resultTypes)
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.Return src count) ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.ATyped (returnedState s ambient rest f.vals) ∧
      SourceMachine.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
        (returnedState s ambient rest f.vals) ⦄ := by
  obtain ⟨types, nextTyped, simulation⟩ := epilogue_source s ambient f rest labels typed
  have types' : f.vals.map Compiler.valueType = f.resultTypes := by
    have equal : Compiler.valueType = SourceMachine.valueType := by
      funext value
      cases value with
      | REF_NULL ty => cases ty <;> rfl
      | _ => rfl
    rw [equal, types]
  have bounds : raw.base.val + src.val + count.val ≤ exec.slots.length := by
    simpa only [source, width, List.map_append, Compiler.slots_append, types', Nat.add_assoc] using capacity
  have sourceBound : raw.base.val + src.val ≤ Usize.max := by scalar_tac
  have represented : ValuesAt exec.slots.val (raw.base.val + src.val) f.vals := by
    simpa only [source] using ValuesAt.operands slots
  simp only [runtime.interp.dispatch]
  step with return_effect exec raw.base src count bounds sourceBound
    as ⟨result, next, success, effect⟩
  exact ⟨success, effect, effect.results represented (by rw [types', width]) bounds, nextTyped, simulation⟩

/-- Complete fetched epilogue iteration with exact frame removal. -/
theorem step_epilogue_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Return src count))
    (pcBound : raw.pc.val < U32.max)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Compiler.slots (f.locals.map Compiler.valueType))
    (width : count.val = Compiler.slots f.resultTypes)
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ≤ exec.slots.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.ATyped (returnedState s ambient rest f.vals) ∧
      SourceMachine.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
        (returnedState s ambient rest f.vals) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.Return src count) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_epilogue_refines memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw src count s ambient f rest labels typed slots source width capacity)
  intro out effect
  exact ⟨effect.1, effect.2.1.before_fetch last, effect.2.2⟩

end Itasca.Runtime.Interp
