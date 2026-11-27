import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Compiler.Local.Relations.Select.SelectOperands

open WebAssembly

open Itasca.Representation

/-!
# Function-entry and local execution effects

Epilogue moves, local code points, capacity and typed arguments establish entry-level slot
relations. Select and synthetic-initializer errors retain their corresponding source
causes.
-/

/-! ## Epilogue -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

def resultLabel (types : List valtype) : SourceMachine.Label := ⟨types, types, [], 0, []⟩

/-- Falling off an unlabeled function body returns exactly its declared values,
with a generated FRAME reduction and preservation of caller typing. -/
theorem frame_end_source (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame)
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
theorem epilogue_source (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame)
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
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Representation.slots (f.locals.map Representation.valueType))
    (width : count.val = Representation.slots f.resultTypes)
    (capacity : raw.base.val + Representation.slots ((f.locals ++ f.vals).map Representation.valueType) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.Return src count) ⦃ out =>
      out.1 = .Ok () ∧ ReturnEffect exec out.2.1 raw.base.val src.val count.val ∧
      ValuesAt out.2.1.slots.val raw.base.val f.vals ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.ATyped (returnedState s ambient rest f.vals) ∧
      SourceMachine.NextSim ⟨s, ambient, { f with code := [] } :: rest, []⟩
        (returnedState s ambient rest f.vals) ⦄ := by
  obtain ⟨types, nextTyped, simulation⟩ := epilogue_source s ambient f rest labels typed
  have types' : f.vals.map Representation.valueType = f.resultTypes := by
    have equal : Representation.valueType = SourceMachine.valueType := by
      funext value
      cases value with
      | REF_NULL ty => cases ty <;> rfl
      | _ => rfl
    rw [equal, types]
  have bounds : raw.base.val + src.val + count.val ≤ exec.slots.length := by
    simpa only [source, width, List.map_append, Representation.slots_append, types', Nat.add_assoc] using capacity
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
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (labels : f.labels = [] ∨ f.labels = [resultLabel f.resultTypes])
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [] } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (source : src.val = Representation.slots (f.locals.map Representation.valueType))
    (width : count.val = Representation.slots f.resultTypes)
    (capacity : raw.base.val + Representation.slots ((f.locals ++ f.vals).map Representation.valueType) ≤ exec.slots.length) :
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

end Itasca.Interp

end

/-! ## Move -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- The actual scalar/vector transfer emitted for a local copies exactly the
value's width and preserves every non-slot execution field, store and platform. -/
theorem dispatch_move_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (ty : valtype) (dst src : U32)
    (source : base.val + src.val + Representation.width ty ≤ exec.slots.length)
    (destination : base.val + dst.val + Representation.width ty ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.move ty dst src) ⦃ out =>
        out.1 = .Ok () ∧ SlotsEffect exec out.2.1
          (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) (Representation.width ty)) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  by_cases vector : Representation.width ty = 2
  · have hs : base.val + src.val + 2 ≤ exec.slots.length := by omega
    have hd : base.val + dst.val + 2 ≤ exec.slots.length := by omega
    simp only [Compiler.move, if_pos vector, runtime.interp.dispatch]
    obtain ⟨out, result, success, slots⟩ := WP.spec_imp_exists
      (copy2_effect exec base dst src hs hd)
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [vector] using slots, rfl, rfl⟩
  · have scalar : Representation.width ty = 1 := by cases ty <;> simp_all [Representation.width]
    have hs : base.val + src.val < exec.slots.length := by omega
    have hd : base.val + dst.val < exec.slots.length := by omega
    simp only [Compiler.move, if_neg vector, runtime.interp.dispatch]
    obtain ⟨out, result, success, slots⟩ := WP.spec_imp_exists
      (copy_effect exec base dst src hs hd)
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [scalar, copyWords] using slots, rfl, rfl⟩

end Itasca.Interp

end

/-! ## LocalCodePoint -/

section

/-!
Local get/write copies and their emitted-code points. ValuesAt transport proves the concrete local operations before inversion identifies the corresponding linear emission.
-/

/-! ## Local -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem dispatch_local_get_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (value : val)
    (lookup : f.locals[index.val]? = some value)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front })
    (source : src.val = Representation.offset (f.locals.map Representation.valueType) index.val)
    (destination : dst.val = Representation.slots ((f.locals ++ front).map Representation.valueType))
    (capacity : raw.base.val + dst.val + Representation.width (Representation.valueType value) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Compiler.move (Representation.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [value] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Representation.valueType)[index.val]? = some (Representation.valueType value) := by
    simpa using congrArg (Option.map Representation.valueType) lookup
  have localEnd := Representation.offset_add_width_le typeLookup
  have stackLength : (Representation.encodeValues (f.locals ++ front)).length = dst.val := by
    rw [Representation.encode_values_length, destination]
  have order : raw.base.val + src.val + (Representation.encodeValue value).length ≤ raw.base.val + dst.val := by
    rw [Representation.encode_value_length, source, destination]
    simp only [List.map_append, Representation.slots_append]
    omega
  have sourceBound : raw.base.val + src.val + Representation.width (Representation.valueType value) ≤ exec.slots.length := by
    rw [Representation.encode_value_length] at order
    omega
  have values : ValuesAt exec.slots.val raw.base.val (f.locals ++ front) := slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Representation.encodeValue value) := by
    simpa only [source] using values.locals.lookup lookup
  have represented := WordsAt.copy_append values input
    (by rw [stackLength]; exact Or.inr order)
    (by simpa only [Representation.encode_value_length] using sourceBound)
    (by simpa only [stackLength, Representation.encode_value_length] using capacity)
  rw [stackLength] at represented
  have step : SourceMachine.astep ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ := by
    simp only [SourceMachine.astep, lookup, SourceMachine.advance]
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front } rest
    (.LOCAL_GET (.mk_uN index.val)) after _ (.local_get _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Representation.valueType value) dst src sourceBound capacity)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  have result : ValuesAt out.2.1.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    rw [written]
    simpa only [ValuesAt, Representation.encode_values_append, Representation.encodeValues, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Representation.encode_value_length] using represented
  simpa only [FrameSlots, List.append_assoc] using result

end Itasca.Interp

end

/-! ## Local Regions -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- A same-type local replacement changes exactly that local's encoded region.
The remaining local values and the operand stack retain their word addresses. -/
theorem ValuesAt.copy_local {words : List U64} {base src index : Nat}
    {locals stack : List val} {old replacement : val}
    (live : ValuesAt words base (locals ++ stack))
    (lookup : locals[index]? = some old)
    (typed : Representation.valueType replacement = Representation.valueType old)
    (input : WordsAt words src (Representation.encodeValue replacement))
    (order : base + Representation.offset (locals.map Representation.valueType) index ≤ src ∨
      src + (Representation.encodeValue replacement).length ≤ base + Representation.offset (locals.map Representation.valueType) index)
    (source : src + (Representation.encodeValue replacement).length ≤ words.length)
    (destination : base + Representation.offset (locals.map Representation.valueType) index +
      (Representation.encodeValue replacement).length ≤ words.length) :
    ValuesAt (copyWords words (base + Representation.offset (locals.map Representation.valueType) index)
      src (Representation.encodeValue replacement).length) base (locals.set index replacement ++ stack) := by
  have bound : index < locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have oldEq : locals[index] = old := List.getElem?_eq_some_iff.mp lookup |>.2
  have self : locals.set index old = locals := by
    rw [← oldEq]
    exact List.set_getElem_self bound
  have split := Compiler.encode_values_set bound old
  rw [self] at split
  have offsetBound : Representation.offset (locals.map Representation.valueType) index ≤ (Representation.encodeValues locals).length := by
    rw [Representation.encode_values_length]
    exact Representation.offset_le _ _
  have length : ((Representation.encodeValues locals).take (Representation.offset (locals.map Representation.valueType) index)).length =
      Representation.offset (locals.map Representation.valueType) index := by
    simp only [List.length_take, Nat.min_eq_left offsetBound]
  have region : WordsAt words base
      ((Representation.encodeValues locals).take (Representation.offset (locals.map Representation.valueType) index) ++
      Representation.encodeValue old ++
      ((Representation.encodeValues locals).drop (Representation.offset (locals.map Representation.valueType) (index + 1)) ++ Representation.encodeValues stack)) := by
    have full : WordsAt words base (Representation.encodeValues locals ++ Representation.encodeValues stack) := by
      simpa only [ValuesAt, Representation.encode_values_append] using live
    rw [split] at full
    simpa only [List.append_assoc] using full
  have widths : (Representation.encodeValue replacement).length = (Representation.encodeValue old).length := by
    simp only [Representation.encode_value_length, typed]
  have changed := WordsAt.copy_replace region input widths
    (by simpa only [length] using order)
    source (by simpa only [length] using destination)
  rw [length] at changed
  have updated := Compiler.encode_values_set bound replacement
  simp only [ValuesAt, Representation.encode_values_append, updated]
  simpa only [List.append_assoc] using changed

end Itasca.Interp

end

/-! ## Local Write -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- LOCAL_SET and LOCAL_TEE use the same concrete transfer. Only their live
operand-stack boundary differs; the source step derives from typed execution. -/
theorem dispatch_local_write_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32) (keep : Bool)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (value old : val)
    (lookup : f.locals[index.val]? = some old)
    (compatible : Representation.valueType value = Representation.valueType old)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after,
      vals := front ++ [value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [value] })
    (source : src.val = Representation.slots ((f.locals ++ front).map Representation.valueType))
    (destination : dst.val = Representation.offset (f.locals.map Representation.valueType) index.val) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Compiler.move (Representation.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Representation.valueType)[index.val]? = some (Representation.valueType old) := by
    simpa using congrArg (Option.map Representation.valueType) lookup
  have localEnd := Representation.offset_add_width_le typeLookup
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Representation.encodeValue value) := by
    simpa only [ValuesAt, source, Representation.encodeValues, List.flatMap_cons, List.flatMap_nil, List.append_nil] using allValues.operands
  have nonempty : 0 < (Representation.encodeValue value).length := by
    rw [Representation.encode_value_length]
    exact Representation.width_positive _
  have sourceBound : raw.base.val + src.val + (Representation.encodeValue value).length ≤ exec.slots.length := by
    have bound := (input ((Representation.encodeValue value).length - 1) (by omega)).1
    change raw.base.val + src.val + ((Representation.encodeValue value).length - 1) < exec.slots.length at bound
    omega
  have order : raw.base.val + dst.val + (Representation.encodeValue value).length ≤ raw.base.val + src.val := by
    rw [Representation.encode_value_length, compatible, source, destination]
    simp only [List.map_append, Representation.slots_append]
    omega
  have destinationBound : raw.base.val + dst.val + (Representation.encodeValue value).length ≤ exec.slots.length := by omega
  have live : ValuesAt exec.slots.val raw.base.val
      (f.locals ++ (if keep then front ++ [value] else front)) := by
    cases keep with
    | false => exact allValues.locals
    | true => exact slots
  have changed := ValuesAt.copy_local live lookup compatible input
    (by rw [← destination]; exact Or.inl (by omega)) sourceBound
    (by simpa only [destination] using destinationBound)
  rw [← destination] at changed
  have type_eq (v : val) : Representation.valueType v = SourceMachine.valueType v := by
    cases v with
    | REF_NULL rt => cases rt <;> rfl
    | _ => rfl
  have compatible' : SourceMachine.valueType value = SourceMachine.valueType old := by
    simpa only [type_eq] using compatible
  have step : SourceMachine.astep
      ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ := by
    cases keep <;> simp [SourceMachine.astep, SourceMachine.pop_append, lookup, compatible', SourceMachine.advance]
  have simulation : SourceMachine.NextSim
      ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
      ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ := by
    cases keep with
    | false =>
      exact SourceMachine.instruction_simulation s ambient { f with vals := front ++ [value] } rest
        (.LOCAL_SET (.mk_uN index.val)) after _ (.local_set _) typed step
    | true =>
      exact SourceMachine.instruction_simulation s ambient { f with vals := front ++ [value] } rest
        (.LOCAL_TEE (.mk_uN index.val)) after _ (.local_tee _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Representation.valueType value) dst src
    (by simpa only [Representation.encode_value_length] using sourceBound)
    (by simpa only [Representation.encode_value_length] using destinationBound))
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  simp only [FrameSlots]
  rw [written]
  simpa only [Representation.encode_value_length] using changed

end Itasca.Interp

end

/-! ## Local Code Point -/

section

namespace Itasca.Interp
open Aeneas.Std

theorem linear_emission_local_get_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (index : Nat) (h : Compiler.LinearEmission locals before (.LOCAL_GET (.mk_uN index)) emitted after) :
    ∃ ty localSlot stackSlot,
      locals[index]? = some ty ∧
      emitted = [Compiler.move ty stackSlot localSlot] ∧ after = before ++ [ty] ∧
      localSlot.val = Representation.offset locals index ∧
      stackSlot.val = Representation.slots locals + Representation.slots before := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at h
  cases h with
  | localGet stack ty idx localSlot stackSlot hty hlocal hstack =>
    simp only [instr.LOCAL_GET.injEq, uN.mk_uN.injEq] at equality
    subst index
    exact ⟨ty, localSlot, stackSlot, hty, rfl, rfl, hlocal, hstack⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linear_emission_local_write_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (index : Nat) (keep : Bool)
    (h : Compiler.LinearEmission locals before
      (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    ∃ stack ty localSlot stackSlot,
      before = stack ++ [ty] ∧ locals[index]? = some ty ∧
      emitted = [Compiler.move ty localSlot stackSlot] ∧ after = (if keep then stack ++ [ty] else stack) ∧
      localSlot.val = Representation.offset locals index ∧
      stackSlot.val = Representation.slots locals + Representation.slots stack := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at h
  cases h with
  | localSet stack ty idx localSlot stackSlot hty hlocal hstack =>
    cases keep with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, instr.LOCAL_SET.injEq, uN.mk_uN.injEq] at equality
      subst index
      exact ⟨_, ty, localSlot, stackSlot, rfl, hty, rfl, rfl, hlocal, hstack⟩
    | true => simp at equality
  | localTee stack ty idx localSlot stackSlot hty hlocal hstack =>
    cases keep with
    | false => simp at equality
    | true =>
      simp only [↓reduceIte, instr.LOCAL_TEE.injEq, uN.mk_uN.injEq] at equality
      subst index
      exact ⟨_, ty, localSlot, stackSlot, rfl, hty, rfl, rfl, hlocal, hstack⟩
  | binary stack ity op left right hl hr => cases keep <;> cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    cases keep <;> simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases keep <;> simp_all

end Itasca.Interp

end

end

/-! ## LocalCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem move_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (move ty dst src) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val ∧ src.val + width ty ≤ compiled.slot_count.val := by
  cases ty <;> simp only [move, width, reduceIte] at checked ⊢
  all_goals first | exact copy_valid_bounds compiled dst src checked | exact copy2_valid_bounds compiled dst src checked

end Itasca.Compiler

end

/-! ## TypedArguments -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

theorem source_type_injective : Function.Injective Itasca.Translation.valueType := by
  intro left right same
  cases left <;> cases right <;> simp_all [Itasca.Translation.valueType]

theorem _root_.Itasca.Representation.ValueOwnedFits.owned {id : Usize} {value : runtime.Value}
    (owned : ValueOwnedFits id value) : OwnedBy id value := by
  cases value <;> simp_all [ValueOwnedFits, OwnedBy]
  all_goals cases ‹Option _› <;> simp_all [ValueOwnedFits, OwnedBy]

/-- Source-typed arguments with issued identities satisfy the concrete checker.
This is independent of the subsequent call and interpreter execution. -/
theorem typed_arguments_match {s : WebAssembly.store} {id : Usize}
    {args : List runtime.Value} {types : List Itasca.wasm_types.ValueType}
    (typed : ResultsTyped s (types.map Itasca.Translation.valueType) (args.map sourceValue))
    (owned : ∀ value ∈ args, ValueOwnedFits id value) :
    List.Forall₂ (ArgumentMatches id) args types := by
  have tags : args.map rawType = types := by
    apply List.map_injective_iff.mpr source_type_injective
    have tags := SourceMachine.results_type_of_typed typed
    simpa only [List.map_map, show SourceMachine.valueType = Representation.valueType from (funext value_type_eq_abs).symm,
      Function.comp_def, source_value_type] using tags
  induction args generalizing types with
  | nil => cases types <;> simp_all
  | cons value args ih =>
    cases types with
    | nil => simp at tags
    | cons ty types =>
      simp only [List.map_cons, List.cons.injEq] at tags
      apply List.Forall₂.cons
      · exact ⟨(owned value (by simp)).owned, tags.1⟩
      · apply ih
        · cases typed with | cons _ tail => exact tail
        · intro v member; exact owned v (by simp [member])
        · exact tags.2

/-- The actual argument-checking function accepts source-typed owned inputs. -/
theorem typed_arguments_accepted {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (sourceStore : WebAssembly.store)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (typed : ResultsTyped sourceStore (types.val.map Itasca.Translation.valueType) (args.val.map sourceValue))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value) :
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ()) := by
  obtain ⟨answer, checked, accepted⟩ := WP.spec_imp_exists
    (check_values_accepts_iff memory store args (alloc.vec.Vec.deref types))
  have matched : List.Forall₂ (ArgumentMatches store.id) args.val (alloc.vec.Vec.deref types).val := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using typed_arguments_match typed owned
  have ok := accepted.mpr matched
  simpa only [ok] using checked
end Itasca.Interp

end

/-! ## InitializerErrors -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem synthetic_initializer_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (width : code.slot_count.val = words.length)
    (hcode : code.code.val = [instruction, .Return 0#u32 code.slot_count]) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → ∃ resource, error = .Exhausted resource) ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    have exhausted : ∃ resource, error = .Exhausted resource := by
      cases error <;> simp_all only [EnsureEffect]
      rename_i resource
      exact ⟨resource, rfl⟩
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using exhausted
  | Ok unit =>
    cases unit
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate words.length 0#u64 := by
      simpa [alloc.vec.Vec.new, width] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have capacity : words.length ≤ prepared.slots.length := by
        simp [alloc.vec.Vec.length, slots]
      step with synthetic_loop_initializer memory hooks floats allocator
        { prepared with frames := pushed } store platform instIndex function inst code instruction words
        code.slot_count hi hc read capacity (by simpa [width] using capacity) pushedFrames hcode
        as ⟨store', platform', finalSlots, result, hs, hp, hwords, hok⟩
      subst store' platform' result
      have finalWords : finalSlots.val = words := by
        rw [slots, read.zero_slots] at hwords
        exact hwords
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with get_effect finalSlots.deref 0#usize as ⟨lo, hlo⟩
      step with get_effect finalSlots.deref 1#usize as ⟨hi, hhi⟩
      have low : lo = (words[0]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hlo
      have high : hi = (words[1]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hhi
      simp [low, high]

theorem synthetic_resolved_initializer_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : InitializerResolution store inst expr ty words) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → ∃ resource, error = .Exhausted resource) ⦄ := by
  obtain ⟨instruction, hop, hcode⟩ := compiled.code
  apply synthetic_initializer_errors memory hooks floats allocator law store platform instIndex function
    inst code instruction words hi hc (resolved.read code instruction hop)
    (by rw [compiled.capacity]; exact resolved.width)
  simpa [compiled.capacity] using hcode

end Itasca.Interp

end

/-! ## SelectSlots -/

section

/-!
Select execution and destination-slot representation. The concrete choice and value layout establish the resulting selected value without changing unrelated slots.
-/

/-! ## Select -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

@[step] theorem select_effect (exec : runtime.interp.Execution) (base : Usize) (left right condition : U32)
    (hc : base.val+condition.val < exec.slots.length)
    (hl : base.val+left.val < exec.slots.length)
    (hr : base.val+right.val < exec.slots.length) :
    runtime.interp.execute_select exec base left right condition ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (if UScalar.cast .U32 exec.slots.val[base.val+condition.val]! = 0#u32
         then copyWords exec.slots.val (base.val+left.val) (base.val+right.val) 1
         else exec.slots.val) ⦄ := by
  unfold runtime.interp.execute_select
  step* <;> simp_all [SlotsEffect,copyWords,_root_.getElem!_pos]

@[step] theorem select2_effect (exec : runtime.interp.Execution) (base : Usize) (left right condition : U32)
    (hc : base.val+condition.val < exec.slots.length)
    (hl : base.val+left.val+2 ≤ exec.slots.length)
    (hr : base.val+right.val+2 ≤ exec.slots.length) :
    runtime.interp.execute_select2 exec base left right condition ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (if UScalar.cast .U32 exec.slots.val[base.val+condition.val]! = 0#u32
         then copyWords exec.slots.val (base.val+left.val) (base.val+right.val) 2
         else exec.slots.val) ⦄ := by
  unfold runtime.interp.execute_select2
  simp only [lift,bind_ok,alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect,_root_.getElem!_pos] <;> first | assumption | omega
end Itasca.Interp

end

/-! ## Select Slots -/

section

set_option maxHeartbeats 1000000
namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem select_slots {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (front : List val) (left right : val) (bits : Nat)
    (a b condition : U32) (ty : valtype)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ [left,right,SourceMachine.integerVal .I32 bits]))
    (leftType : Representation.valueType left = ty) (rightType : Representation.valueType right = ty)
    (leftPos : a.val = Representation.slots (front.map Representation.valueType))
    (rightPos : b.val = a.val+Representation.width ty) (conditionPos : condition.val = b.val+Representation.width ty)
    (bitsBound : bits < 2^32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index raw.instance raw.function raw.base
      (Compiler.selectInstruction (decide (Representation.width ty = 2)) a b condition) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ValuesAt out.2.1.slots.val raw.base.val (front ++ [if bits = 0 then right else left]) ∧
      {out.2.1 with slots := exec.slots} = exec ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have words : WordsAt exec.slots.val raw.base.val
      ((Representation.encodeValues front ++ Representation.encodeValue left ++ Representation.encodeValue right) ++ [bits]) := by
    simpa only [ValuesAt,Representation.encode_values_append,Representation.encodeValues,Representation.encodeValue,SourceMachine.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using values
  have frontLength : (Representation.encodeValues front).length = a.val := by rw [Representation.encode_values_length,leftPos]
  have leftLength : (Representation.encodeValue left).length = Representation.width ty := by rw [Representation.encode_value_length,leftType]
  have rightLength : (Representation.encodeValue right).length = Representation.width ty := by rw [Representation.encode_value_length,rightType]
  have conditionLength : (Representation.encodeValues front ++ Representation.encodeValue left ++ Representation.encodeValue right).length = condition.val := by
    simp only [List.length_append,frontLength,leftLength,rightLength]
    omega
  obtain ⟨bound,wordEq⟩ := words.append_right 0 (by simp)
  have hc : raw.base.val+condition.val < exec.slots.length := by simpa only [conditionLength,Nat.add_zero] using bound
  have conditionWord : exec.slots.val[raw.base.val+condition.val]!.val = bits := by
    simpa only [conditionLength,Nat.add_zero,List.getElem!_cons_zero] using wordEq
  have castEq : (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = bits := by scalar_tac
  have zeroEq : (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]! = 0#u32) ↔ bits = 0 := by
    constructor
    · intro eq; have v := congrArg UScalar.val eq; change (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = 0 at v; rwa [castEq] at v
    · intro eq; apply UScalar.eq_of_val_eq; change (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = 0; rw [castEq,eq]
  have widthPositive := Representation.width_positive ty
  have sourceBound : raw.base.val+b.val+Representation.width ty ≤ exec.slots.length := by omega
  have destinationBound : raw.base.val+a.val+Representation.width ty ≤ exec.slots.length := by omega
  have representation : ∀ newWords,
      newWords = (if bits = 0 then copyWords exec.slots.val (raw.base.val+a.val) (raw.base.val+b.val) (Representation.width ty) else exec.slots.val) →
      ValuesAt newWords raw.base.val (front ++ [if bits = 0 then right else left]) ∧
      SlotPrefix raw.base.val exec.slots.val newWords := by
    intro newWords effect
    rw [effect]
    by_cases zero : bits = 0
    · rw [if_pos zero,if_pos zero]
      have input : WordsAt exec.slots.val (raw.base.val+b.val) (Representation.encodeValue right) := by
        have last := words.append_left.append_right
        simpa only [List.length_append,frontLength,leftLength,← rightPos,Nat.add_assoc] using last
      have copied := words.append_left.append_left.append_left.copy_append input
        (Or.inl (by omega)) (by simpa only [rightLength] using sourceBound)
        (by simpa only [frontLength,rightLength] using destinationBound)
      refine ⟨?_,SlotPrefix.copy raw.base.val exec.slots.val (raw.base.val+a.val) (raw.base.val+b.val) (Representation.width ty) (by omega)⟩
      rw [frontLength,rightLength] at copied
      simpa only [ValuesAt,Representation.encode_values_append,Representation.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,frontLength,rightLength] using copied
    · rw [if_neg zero,if_neg zero]
      refine ⟨?_,.refl _ _⟩
      simpa only [ValuesAt,Representation.encode_values_append,Representation.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using words.append_left.append_left
  have scalarWidth : Representation.width ty = 1 ∨ Representation.width ty = 2 := by cases ty <;> decide
  rcases scalarWidth with width | width
  · have narrow : decide (Representation.width ty = 2) = false := by simp [width]
    rw [show Compiler.selectInstruction (decide (Representation.width ty = 2)) a b condition = .Select a b condition by simp [narrow,Compiler.selectInstruction]]
    simp only [runtime.interp.dispatch]
    obtain ⟨out,result,success,changed,fields⟩ := WP.spec_imp_exists
      (select_effect exec raw.base a b condition hc (by omega) (by omega))
    rw [result,bind_ok]
    rcases out with ⟨status,updated⟩
    with_unfolding_all apply WP.spec.ret
    have converted := changed
    simp only [zeroEq] at converted
    have fresh := representation updated.slots.val (by simpa only [width] using converted)
    exact ⟨success,rfl,rfl,fresh.1,fields,fresh.2⟩
  · have wide : decide (Representation.width ty = 2) = true := by simp [width]
    rw [show Compiler.selectInstruction (decide (Representation.width ty = 2)) a b condition = .Select2 a b condition by simp [wide,Compiler.selectInstruction]]
    simp only [runtime.interp.dispatch]
    obtain ⟨out,result,success,changed,fields⟩ := WP.spec_imp_exists
      (select2_effect exec raw.base a b condition hc (by omega) (by omega))
    rw [result,bind_ok]
    rcases out with ⟨status,updated⟩
    with_unfolding_all apply WP.spec.ret
    have converted := changed
    simp only [zeroEq] at converted
    have fresh := representation updated.slots.val (by simpa only [width] using converted)
    exact ⟨success,rfl,rfl,fresh.1,fields,fresh.2⟩
end Itasca.Interp

end

end

/-! ## SyntheticInitializerCauses -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem synthetic_initializer_resource_causes (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (width : code.slot_count.val = words.length)
    (hcode : code.code.val = [instruction, .Return 0#u32 code.slot_count]) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → SyntheticPreparationCause allocator store code error) ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    have cause : SyntheticPreparationCause allocator store code error := by
      cases error <;> simp only [EnsureEffect] at ensured <;> try contradiction
      rename_i resource
      cases resource <;> simp only [EnsureEffect] at ensured <;> try contradiction
      · exact ensured.1
      · obtain ⟨within,needed,same,n,amount,refused⟩ := ensured
        have nEq : n = UScalar.cast .Usize code.slot_count := by
          apply UScalar.eq_of_val_eq
          simpa [alloc.vec.Vec.new,alloc.vec.Vec.length] using amount
        exact Or.inl (by simpa only [nEq] using refused)
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using cause
  | Ok unit =>
    cases unit
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate words.length 0#u64 := by
      simpa [alloc.vec.Vec.new, width] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      have frameEq : prepared.frames = alloc.vec.Vec.new runtime.interp.Frame := alloc.vec.Vec.ext _ _ frames
      have cause : SyntheticPreparationCause allocator store code (.Exhausted .Allocation) :=
        Or.inr (by simpa only [frameEq] using reserved)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using cause
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have capacity : words.length ≤ prepared.slots.length := by
        simp [alloc.vec.Vec.length, slots]
      step with synthetic_loop_initializer memory hooks floats allocator
        { prepared with frames := pushed } store platform instIndex function inst code instruction words
        code.slot_count hi hc read capacity (by simpa [width] using capacity) pushedFrames hcode
        as ⟨store', platform', finalSlots, result, hs, hp, hwords, hok⟩
      subst store' platform' result
      have finalWords : finalSlots.val = words := by
        rw [slots, read.zero_slots] at hwords
        exact hwords
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with get_effect finalSlots.deref 0#usize as ⟨lo, hlo⟩
      step with get_effect finalSlots.deref 1#usize as ⟨hi, hhi⟩
      have low : lo = (words[0]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hlo
      have high : hi = (words[1]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hhi
      simp [low, high]

theorem synthetic_resolved_initializer_resource_causes (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : InitializerResolution store inst expr ty words) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → SyntheticPreparationCause allocator store code error) ⦄ := by
  obtain ⟨instruction, hop, hcode⟩ := compiled.code
  apply synthetic_initializer_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code instruction words hi hc (resolved.read code instruction hop)
    (by rw [compiled.capacity]; exact resolved.width)
  simpa [compiled.capacity] using hcode

end Itasca.Interp

end
