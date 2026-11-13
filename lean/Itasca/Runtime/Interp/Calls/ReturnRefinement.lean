import Itasca.Runtime.Interp.Calls.DirectCall
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Relations.Fetch

/-!
Sections, each formerly its own module: CallRegions, CallFrames, ReturnRegions, ReturnRefinement.
-/

/-! ## CallRegions -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem WordsAt.extend {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (extra : List U64) : WordsAt (words ++ extra) base bits := by
  intro j hj
  obtain ⟨bound, value⟩ := h j hj
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  simpa only [List.getElem!_append_left words extra (base + j) bound] using value

theorem WordsAt.zero_preserves {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (start count : Nat) (bound : start + count ≤ words.length)
    (outside : base + bits.length ≤ start ∨ start + count ≤ base) :
    WordsAt (zeroWords words start count) base bits := by
  apply h.congr_region (zero_words_length _ _ _)
  intro j hj
  exact (zero_words_effect words start count bound).2 _ (by omega)

theorem zero_words_represents (words : List U64) (start count : Nat)
    (bound : start + count ≤ words.length) :
    WordsAt (zeroWords words start count) start (List.replicate count 0) := by
  intro j hj
  have hj' : j < count := by simpa only [List.length_replicate] using hj
  have word := (zero_words_effect words start count bound).1 j hj'
  have valid : start + j < (zeroWords words start count).length := by rw [zero_words_length]; omega
  refine ⟨valid, ?_⟩
  rw [List.getElem?_eq_getElem valid] at word
  rw [_root_.getElem!_pos (zeroWords words start count) (start + j) valid, Option.some.inj word]
  simp [hj']

/-- Exact call initialization preserves parameter words and supplies the
zero encoding of all declared non-parameter locals. -/
theorem CallEntryEffect.callee_values
    {before after : runtime.interp.Execution} {instanceIndex functionIndex base : Usize}
    {code : runtime.bytecode.CompiledFunction} {args defaults : List val} {localTypes : List valtype}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code)
    (arguments : ValuesAt before.slots.val base.val args)
    (parameters : code.param_slots.val = Compiler.slots (args.map Compiler.valueType))
    (locals : code.local_slots.val = code.param_slots.val + Compiler.slots localTypes)
    (capacity : code.local_slots.val ≤ code.slot_count.val)
    (default : SourceMachine.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    ValuesAt after.slots.val base.val (args ++ defaults) := by
  obtain ⟨_, slots, _⟩ := effect
  have bound : base.val + code.param_slots.val + Compiler.slots localTypes ≤
      (before.slots.val ++ List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64).length := by
    simp only [List.length_append, List.length_replicate]
    change base.val + code.param_slots.val + Compiler.slots localTypes ≤
      before.slots.length + (base.val + code.slot_count.val - before.slots.length)
    omega
  have initialized := zero_words_represents
    (before.slots.val ++ List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64)
    (base.val + code.param_slots.val) (Compiler.slots localTypes) bound
  have saved := (WordsAt.extend arguments
    (List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64)).zero_preserves
    (base.val + code.param_slots.val) (Compiler.slots localTypes) bound
    (Or.inl (by rw [Compiler.encode_values_length, parameters]))
  have full := WordsAt.append saved (by simpa only [Compiler.encode_values_length, parameters] using initialized)
  simp only [ValuesAt, Compiler.encode_values_append, encode_default_locals localTypes defaults default]
  rw [slots]
  have count : code.local_slots.val - code.param_slots.val = Compiler.slots localTypes := by omega
  simpa only [count] using full

/-- Calling a defined function leaves every suspended caller word below the
callee argument base intact, even when invocation storage has to grow. -/
theorem CallEntryEffect.preserve_prefix
    {before after : runtime.interp.Execution} {instanceIndex functionIndex base : Usize}
    {code : runtime.bytecode.CompiledFunction} {position : Nat} {bits : List Nat}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code)
    (represented : WordsAt before.slots.val position bits)
    (below : position + bits.length ≤ base.val)
    (params : code.param_slots.val ≤ code.local_slots.val)
    (capacity : code.local_slots.val ≤ code.slot_count.val) :
    WordsAt after.slots.val position bits := by
  obtain ⟨_, slots, _⟩ := effect
  rw [slots]
  apply (represented.extend _).zero_preserves
  · simp only [List.length_append, List.length_replicate]
    change base.val + code.param_slots.val + (code.local_slots.val - code.param_slots.val) ≤
      before.slots.length + (base.val + code.slot_count.val - before.slots.length)
    omega
  · exact Or.inl (by omega)

end Itasca.Runtime.Interp

end

/-! ## CallFrames -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem CallEntryEffect.slots_length {before after : runtime.interp.Execution}
    {instanceIndex functionIndex base : Usize} {code : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code) :
    before.slots.length ≤ after.slots.length ∧ base.val + code.slot_count.val ≤ after.slots.length := by
  change before.slots.val.length ≤ after.slots.val.length ∧ _ ≤ after.slots.val.length
  rw [effect.2.1, zero_words_length, List.length_append, List.length_replicate]
  simp only [alloc.vec.Vec.length, alloc.vec.Vec.val]
  omega

/-- Entering a callee retains every existing frame's module/function binding
and allocated capacity. Suspended operand contents are handled separately. -/
theorem CallEntryEffect.preserve_binding {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {instanceIndex functionIndex base : Usize}
    {code : runtime.bytecode.CompiledFunction} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (effect : CallEntryEffect before after instanceIndex functionIndex base code)
    (binding : FrameBinding store before raw source) : FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, member, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, hm, hr, hl, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · rw [effect.1]
    exact List.mem_append_left _ member
  · exact bound.trans effect.slots_length.1

/-- Exact retained metadata for the newly pushed callee. -/
theorem CallEntryEffect.callee_binding {M : Type}
    (store : runtime.store.Store M) (before after : runtime.interp.Execution)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex base : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (args defaults : List val) (body : List instr)
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (identity : before.store = store.id)
    (localTypes : (args ++ defaults).map Compiler.valueType = compiled.locals.val.map sourceType)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled) :
    FrameBinding store after ⟨instanceIndex, functionIndex, 0#u32, base⟩
      ⟨address.index.val, signature.results.val.map sourceType, args ++ defaults,
        Store.decodeInstance store inst,
        [⟨signature.results.val.map sourceType, signature.results.val.map sourceType, [], 0, []⟩],
        body, []⟩ := by
  refine ⟨inst, function, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, rfl, rfl, localTypes, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · simp [effect.1]
  · exact effect.slots_length.2

end Itasca.Runtime.Interp

end

/-! ## ReturnRegions -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Successful return places exactly the source result words at the callee
base, including the zero-result and overlapping-copy cases. -/
theorem ReturnEffect.results {before after : runtime.interp.Execution}
    {base src count : Nat} {values : List val}
    (effect : ReturnEffect before after base src count)
    (represented : ValuesAt before.slots.val (base + src) values)
    (width : count = Compiler.slots (values.map Compiler.valueType))
    (bounds : base + src + count ≤ before.slots.length) :
    ValuesAt after.slots.val base values := by
  rw [ValuesAt, effect.1]
  have size : (Compiler.encodeValues values).length = count := by rw [Compiler.encode_values_length, width]
  have copied := represented.copy base (Or.inl (by omega)) (by rw [size]; exact Nat.le_trans (by omega) bounds)
  simpa only [size] using copied

/-- Return preserves every region below the return destination. -/
theorem ReturnEffect.preserve_prefix {before after : runtime.interp.Execution}
    {base src count position : Nat} {bits : List Nat}
    (effect : ReturnEffect before after base src count)
    (represented : WordsAt before.slots.val position bits)
    (below : position + bits.length ≤ base)
    (bounds : base + src + count ≤ before.slots.length) :
    WordsAt after.slots.val position bits := by
  change base + src + count ≤ before.slots.val.length at bounds
  rw [effect.1]
  apply represented.copy_preserves base (base + src) count (Or.inl (by omega)) bounds (by omega)
  intro j hj
  exact Or.inl (by omega)

/-- The caller's saved values and the copied results form its resumed stack. -/
theorem ReturnEffect.resume {before after : runtime.interp.Execution}
    {base src count : Nat} {raw : runtime.interp.Frame} {caller : SourceMachine.AFrame} {results : List val}
    (effect : ReturnEffect before after base src count)
    (saved : FrameSlots before raw caller)
    (represented : ValuesAt before.slots.val (base + src) results)
    (width : count = Compiler.slots (results.map Compiler.valueType))
    (destination : base = raw.base.val + Compiler.slots ((caller.locals ++ caller.vals).map Compiler.valueType))
    (bounds : base + src + count ≤ before.slots.length) :
    FrameSlots after raw { caller with vals := caller.vals ++ results } := by
  have kept := effect.preserve_prefix saved (by rw [Compiler.encode_values_length, destination]) bounds
  have values := effect.results represented width bounds
  have combined := WordsAt.append kept (by simpa only [ValuesAt, Compiler.encode_values_length, ← destination] using values)
  simpa only [FrameSlots, ValuesAt, Compiler.encode_values_append, List.append_assoc] using combined

/-- The popped concrete frame is exactly the most recently entered callee. -/
theorem ReturnEffect.frames {before after : runtime.interp.Execution}
    {base src count : Nat} {frames : List runtime.interp.Frame} {top : runtime.interp.Frame}
    (effect : ReturnEffect before after base src count)
    (stack : before.frames.val = frames ++ [top]) : after.frames.val = frames := by
  rw [effect.2.1, stack, List.dropLast_concat]

/-- Surviving frames retain their bindings and allocated capacity. -/
theorem ReturnEffect.preserve_binding {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base src count : Nat}
    {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (effect : ReturnEffect before after base src count)
    (binding : FrameBinding store before raw source)
    (member : raw ∈ before.frames.val.dropLast) : FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, hm, hr, hl, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · simpa only [effect.2.1] using member
  · change raw.base.val + compiled.slot_count.val ≤ after.slots.val.length
    rw [effect.1, copy_words_length]
    exact bound

end Itasca.Runtime.Interp

end

/-! ## ReturnRefinement -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The abstract state after returning either resumes the immediate caller or
records the final invocation values. -/
def returnedState (s : _root_.store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (results : List val) : SourceMachine.AState :=
  match rest with
  | [] => ⟨s, ambient, [], results⟩
  | caller :: tail => ⟨s, ambient, { caller with vals := caller.vals ++ results } :: tail, []⟩

theorem return_next (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (front results : List val)
    (types : results.map SourceMachine.valueType = f.resultTypes) :
    SourceMachine.astep ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩ =
      .next (returnedState s ambient rest results) := by
  have length : f.resultTypes.length = results.length := by rw [← types, List.length_map]
  cases rest <;> simp [SourceMachine.astep, SourceMachine.returnFrame, SourceMachine.AFrame.arity, length, types, returnedState, SourceMachine.advance]

/-- Return dispatch copies exact results and removes the frame, while its
source transition performs a positive number of reductions through labels. -/
theorem dispatch_return_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (src count : U32)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front results : List val)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩)
    (types : results.map SourceMachine.valueType = f.resultTypes)
    (slots : FrameSlots exec raw { f with vals := front ++ results })
    (source : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (width : count.val = Compiler.slots (results.map Compiler.valueType))
    (bounds : raw.base.val + src.val + count.val ≤ exec.slots.length)
    (sourceBound : raw.base.val + src.val ≤ Usize.max) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Return src count) ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val results ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩
        (returnedState s ambient rest results) ⦄ := by
  have step := return_next s ambient f rest after front results types
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front ++ results } rest
    .RETURN after _ .ret typed step
  have represented : ValuesAt exec.slots.val (raw.base.val + src.val) results := by
    have words : WordsAt exec.slots.val raw.base.val
        (Compiler.encodeValues (f.locals ++ front) ++ Compiler.encodeValues results) := by
      simpa only [FrameSlots, ValuesAt, Compiler.encode_values_append, List.append_assoc] using slots
    simpa only [ValuesAt, Compiler.encode_values_length, source] using words.append_right
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
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front results : List val)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩)
    (types : results.map SourceMachine.valueType = f.resultTypes)
    (slots : FrameSlots exec raw { f with vals := front ++ results })
    (source : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (width : count.val = Compiler.slots (results.map Compiler.valueType))
    (bounds : raw.base.val + src.val + count.val ≤ exec.slots.length)
    (sourceBound : raw.base.val + src.val ≤ Usize.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val results ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
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

end Itasca.Runtime.Interp

end
