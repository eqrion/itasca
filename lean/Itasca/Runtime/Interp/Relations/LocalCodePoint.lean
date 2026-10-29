import Itasca.Runtime.Interp.Relations.Move
import Itasca.Runtime.SourceMachine.Sim.Instruction
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.Numeric.Decode

/-!
Local get/write copies and their emitted-code points. ValuesAt transport proves the concrete local operations before inversion identifies the corresponding linear emission.
-/

/-! ## Local -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_local_get_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (value : val)
    (lookup : f.locals[index.val]? = some value)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front })
    (source : src.val = Compiler.offset (f.locals.map Compiler.valueType) index.val)
    (destination : dst.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (capacity : raw.base.val + dst.val + Compiler.width (Compiler.valueType value) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Compiler.move (Compiler.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [value] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Compiler.valueType)[index.val]? = some (Compiler.valueType value) := by
    simpa using congrArg (Option.map Compiler.valueType) lookup
  have localEnd := Compiler.offset_add_width_le typeLookup
  have stackLength : (Compiler.encodeValues (f.locals ++ front)).length = dst.val := by
    rw [Compiler.encode_values_length, destination]
  have order : raw.base.val + src.val + (Compiler.encodeValue value).length ≤ raw.base.val + dst.val := by
    rw [Compiler.encode_value_length, source, destination]
    simp only [List.map_append, Compiler.slots_append]
    omega
  have sourceBound : raw.base.val + src.val + Compiler.width (Compiler.valueType value) ≤ exec.slots.length := by
    rw [Compiler.encode_value_length] at order
    omega
  have values : ValuesAt exec.slots.val raw.base.val (f.locals ++ front) := slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Compiler.encodeValue value) := by
    simpa only [source] using values.locals.lookup lookup
  have represented := WordsAt.copy_append values input
    (by rw [stackLength]; exact Or.inr order)
    (by simpa only [Compiler.encode_value_length] using sourceBound)
    (by simpa only [stackLength, Compiler.encode_value_length] using capacity)
  rw [stackLength] at represented
  have step : SourceMachine.astep ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ := by
    simp only [SourceMachine.astep, lookup, SourceMachine.advance]
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front } rest
    (.LOCAL_GET (.mk_uN index.val)) after _ (.local_get _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Compiler.valueType value) dst src sourceBound capacity)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  have result : ValuesAt out.2.1.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    rw [written]
    simpa only [ValuesAt, Compiler.encode_values_append, Compiler.encodeValues, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Compiler.encode_value_length] using represented
  simpa only [FrameSlots, List.append_assoc] using result

end Itasca.Runtime.Interp

end

/-! ## Local Regions -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A same-type local replacement changes exactly that local's encoded region.
The remaining local values and the operand stack retain their word addresses. -/
theorem ValuesAt.copy_local {words : List U64} {base src index : Nat}
    {locals stack : List val} {old replacement : val}
    (live : ValuesAt words base (locals ++ stack))
    (lookup : locals[index]? = some old)
    (typed : Compiler.valueType replacement = Compiler.valueType old)
    (input : WordsAt words src (Compiler.encodeValue replacement))
    (order : base + Compiler.offset (locals.map Compiler.valueType) index ≤ src ∨
      src + (Compiler.encodeValue replacement).length ≤ base + Compiler.offset (locals.map Compiler.valueType) index)
    (source : src + (Compiler.encodeValue replacement).length ≤ words.length)
    (destination : base + Compiler.offset (locals.map Compiler.valueType) index +
      (Compiler.encodeValue replacement).length ≤ words.length) :
    ValuesAt (copyWords words (base + Compiler.offset (locals.map Compiler.valueType) index)
      src (Compiler.encodeValue replacement).length) base (locals.set index replacement ++ stack) := by
  have bound : index < locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have oldEq : locals[index] = old := List.getElem?_eq_some_iff.mp lookup |>.2
  have self : locals.set index old = locals := by
    rw [← oldEq]
    exact List.set_getElem_self bound
  have split := Compiler.encode_values_set bound old
  rw [self] at split
  have offsetBound : Compiler.offset (locals.map Compiler.valueType) index ≤ (Compiler.encodeValues locals).length := by
    rw [Compiler.encode_values_length]
    exact Compiler.offset_le _ _
  have length : ((Compiler.encodeValues locals).take (Compiler.offset (locals.map Compiler.valueType) index)).length =
      Compiler.offset (locals.map Compiler.valueType) index := by
    simp only [List.length_take, Nat.min_eq_left offsetBound]
  have region : WordsAt words base
      ((Compiler.encodeValues locals).take (Compiler.offset (locals.map Compiler.valueType) index) ++
      Compiler.encodeValue old ++
      ((Compiler.encodeValues locals).drop (Compiler.offset (locals.map Compiler.valueType) (index + 1)) ++ Compiler.encodeValues stack)) := by
    have full : WordsAt words base (Compiler.encodeValues locals ++ Compiler.encodeValues stack) := by
      simpa only [ValuesAt, Compiler.encode_values_append] using live
    rw [split] at full
    simpa only [List.append_assoc] using full
  have widths : (Compiler.encodeValue replacement).length = (Compiler.encodeValue old).length := by
    simp only [Compiler.encode_value_length, typed]
  have changed := WordsAt.copy_replace region input widths
    (by simpa only [length] using order)
    source (by simpa only [length] using destination)
  rw [length] at changed
  have updated := Compiler.encode_values_set bound replacement
  simp only [ValuesAt, Compiler.encode_values_append, updated]
  simpa only [List.append_assoc] using changed

end Itasca.Runtime.Interp

end

/-! ## Local Write -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- LOCAL_SET and LOCAL_TEE use the same concrete transfer. Only their live
operand-stack boundary differs; the source step derives from typed execution. -/
theorem dispatch_local_write_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32) (keep : Bool)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (value old : val)
    (lookup : f.locals[index.val]? = some old)
    (compatible : Compiler.valueType value = Compiler.valueType old)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after,
      vals := front ++ [value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [value] })
    (source : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (destination : dst.val = Compiler.offset (f.locals.map Compiler.valueType) index.val) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Compiler.move (Compiler.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Compiler.valueType)[index.val]? = some (Compiler.valueType old) := by
    simpa using congrArg (Option.map Compiler.valueType) lookup
  have localEnd := Compiler.offset_add_width_le typeLookup
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Compiler.encodeValue value) := by
    simpa only [ValuesAt, source, Compiler.encodeValues, List.flatMap_cons, List.flatMap_nil, List.append_nil] using allValues.operands
  have nonempty : 0 < (Compiler.encodeValue value).length := by
    rw [Compiler.encode_value_length]
    exact Compiler.width_positive _
  have sourceBound : raw.base.val + src.val + (Compiler.encodeValue value).length ≤ exec.slots.length := by
    have bound := (input ((Compiler.encodeValue value).length - 1) (by omega)).1
    change raw.base.val + src.val + ((Compiler.encodeValue value).length - 1) < exec.slots.length at bound
    omega
  have order : raw.base.val + dst.val + (Compiler.encodeValue value).length ≤ raw.base.val + src.val := by
    rw [Compiler.encode_value_length, compatible, source, destination]
    simp only [List.map_append, Compiler.slots_append]
    omega
  have destinationBound : raw.base.val + dst.val + (Compiler.encodeValue value).length ≤ exec.slots.length := by omega
  have live : ValuesAt exec.slots.val raw.base.val
      (f.locals ++ (if keep then front ++ [value] else front)) := by
    cases keep with
    | false => exact allValues.locals
    | true => exact slots
  have changed := ValuesAt.copy_local live lookup compatible input
    (by rw [← destination]; exact Or.inl (by omega)) sourceBound
    (by simpa only [destination] using destinationBound)
  rw [← destination] at changed
  have type_eq (v : val) : Compiler.valueType v = SourceMachine.valueType v := by
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
    frameIndex raw.instance raw.function raw.base (Compiler.valueType value) dst src
    (by simpa only [Compiler.encode_value_length] using sourceBound)
    (by simpa only [Compiler.encode_value_length] using destinationBound))
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  simp only [FrameSlots]
  rw [written]
  simpa only [Compiler.encode_value_length] using changed

end Itasca.Runtime.Interp

end

/-! ## Local Code Point -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linear_emission_local_get_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (index : Nat) (h : Compiler.LinearEmission locals before (.LOCAL_GET (.mk_uN index)) emitted after) :
    ∃ ty localSlot stackSlot,
      locals[index]? = some ty ∧
      emitted = [Compiler.move ty stackSlot localSlot] ∧ after = before ++ [ty] ∧
      localSlot.val = Compiler.offset locals index ∧
      stackSlot.val = Compiler.slots locals + Compiler.slots before := by
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
      localSlot.val = Compiler.offset locals index ∧
      stackSlot.val = Compiler.slots locals + Compiler.slots stack := by
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

end Itasca.Runtime.Interp

end
