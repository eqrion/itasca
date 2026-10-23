import Exec.Interp.Calls.ReturnRegions
import Exec.Abs.Sim.Instruction
import Exec.Interp.Relations.Fetch


namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The abstract state after returning either resumes the immediate caller or
records the final invocation values. -/
def returnedState (s : _root_.store) (ambient : frame) (rest : List Abs.AFrame)
    (results : List val) : Abs.AState :=
  match rest with
  | [] => ⟨s, ambient, [], results⟩
  | caller :: tail => ⟨s, ambient, { caller with vals := caller.vals ++ results } :: tail, []⟩

theorem return_next (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front results : List val)
    (types : results.map Abs.valueType = f.resultTypes) :
    Abs.astep ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩ =
      .next (returnedState s ambient rest results) := by
  have length : f.resultTypes.length = results.length := by rw [← types, List.length_map]
  cases rest <;> simp [Abs.astep, Abs.returnFrame, Abs.AFrame.arity, length, types, returnedState, Abs.advance]

/-- Return dispatch copies exact results and removes the frame, while its
source transition performs a positive number of reductions through labels. -/
theorem dispatch_return_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front results : List val)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩)
    (types : results.map Abs.valueType = f.resultTypes)
    (slots : FrameSlots exec raw { f with vals := front ++ results })
    (source : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (width : count.val = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src.val + count.val ≤ exec.slots.length)
    (sourceBound : raw.base.val + src.val ≤ Usize.max) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Return src count) ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val results ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩
        (returnedState s ambient rest results) ⦄ := by
  have step := return_next s ambient f rest after front results types
  have simulation := Abs.instruction_simulation s ambient { f with vals := front ++ results } rest
    .RETURN after _ .ret typed step
  have represented : ValuesAt exec.slots.val (raw.base.val + src.val) results := by
    have words : WordsAt exec.slots.val raw.base.val
        (Code.encodeValues (f.locals ++ front) ++ Code.encodeValues results) := by
      simpa only [FrameSlots, ValuesAt, Code.encodeValues_append, List.append_assoc] using slots
    simpa only [ValuesAt, Code.encodeValues_length, source] using words.append_right
  simp only [runtime.interp.dispatch]
  step with return_effect exec raw.base src count bounds sourceBound
    as ⟨result, next, success, effect⟩
  exact ⟨success, effect, effect.results represented width bounds, simulation⟩


/-- Updating the soon-to-be-popped frame's PC has no observable return effect. -/
theorem ReturnEffect.before_fetch {before after : runtime.interp.Execution}
    {index : Usize} {raw : runtime.interp.Frame} {pc : U32} {base src count : Nat}
    (last : index.val + 1 = before.frames.length)
    (effect : ReturnEffect
      { before with frames := before.frames.set index { raw with pc := pc } } after base src count) :
    ReturnEffect before after base src count := by
  refine ⟨effect.1, ?_, ?_⟩
  · rw [effect.2.1]
    simp only [alloc.vec.Vec.set_val_eq]
    rw [List.dropLast_eq_take, List.length_set, List.take_set_of_le (by change before.frames.length - 1 ≤ index.val; omega),
      ← List.dropLast_eq_take]
  · have h := congrArg (fun e : runtime.interp.Execution => { e with frames := before.frames }) effect.2.2
    exact h

/-- One complete extracted RETURN iteration, including instruction fetch and
caller-PC advancement, refines the source return transition. -/
theorem step_return_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Return src count))
    (pcBound : raw.pc.val < U32.max)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front results : List val)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩)
    (types : results.map Abs.valueType = f.resultTypes)
    (slots : FrameSlots exec raw { f with vals := front ++ results })
    (source : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (width : count.val = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src.val + count.val ≤ exec.slots.length)
    (sourceBound : raw.base.val + src.val ≤ Usize.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val results ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩
        (returnedState s ambient rest results) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (.Return src count) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_return_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw src count s ambient f rest after front results typed types slots
    source width bounds sourceBound)
  intro out effect
  exact ⟨effect.1, effect.2.1.before_fetch last, effect.2.2⟩

end Exec.Interp
