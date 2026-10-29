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

theorem dispatch_localGet_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (value : val)
    (lookup : f.locals[index.val]? = some value)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front })
    (source : src.val = Code.offset (f.locals.map Code.valueType) index.val)
    (destination : dst.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (capacity : raw.base.val + dst.val + Code.width (Code.valueType value) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Code.move (Code.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [value] } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Code.valueType)[index.val]? = some (Code.valueType value) := by
    simpa using congrArg (Option.map Code.valueType) lookup
  have localEnd := Code.offset_add_width_le typeLookup
  have stackLength : (Code.encodeValues (f.locals ++ front)).length = dst.val := by
    rw [Code.encodeValues_length, destination]
  have order : raw.base.val + src.val + (Code.encodeValue value).length ≤ raw.base.val + dst.val := by
    rw [Code.encodeValue_length, source, destination]
    simp only [List.map_append, Code.slots_append]
    omega
  have sourceBound : raw.base.val + src.val + Code.width (Code.valueType value) ≤ exec.slots.length := by
    rw [Code.encodeValue_length] at order
    omega
  have values : ValuesAt exec.slots.val raw.base.val (f.locals ++ front) := slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Code.encodeValue value) := by
    simpa only [source] using values.locals.lookup lookup
  have represented := WordsAt.copy_append values input
    (by rw [stackLength]; exact Or.inr order)
    (by simpa only [Code.encodeValue_length] using sourceBound)
    (by simpa only [stackLength, Code.encodeValue_length] using capacity)
  rw [stackLength] at represented
  have step : Abs.astep ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after, vals := front } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := after, vals := front ++ [value] } :: rest, []⟩ := by
    simp only [Abs.astep, lookup, Abs.advance]
  have simulation := Abs.instruction_simulation s ambient { f with vals := front } rest
    (.LOCAL_GET (.mk_uN index.val)) after _ (.local_get _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Code.valueType value) dst src sourceBound capacity)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  have result : ValuesAt out.2.1.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    rw [written]
    simpa only [ValuesAt, Code.encodeValues_append, Code.encodeValues, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Code.encodeValue_length] using represented
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
    (typed : Code.valueType replacement = Code.valueType old)
    (input : WordsAt words src (Code.encodeValue replacement))
    (order : base + Code.offset (locals.map Code.valueType) index ≤ src ∨
      src + (Code.encodeValue replacement).length ≤ base + Code.offset (locals.map Code.valueType) index)
    (source : src + (Code.encodeValue replacement).length ≤ words.length)
    (destination : base + Code.offset (locals.map Code.valueType) index +
      (Code.encodeValue replacement).length ≤ words.length) :
    ValuesAt (copyWords words (base + Code.offset (locals.map Code.valueType) index)
      src (Code.encodeValue replacement).length) base (locals.set index replacement ++ stack) := by
  have bound : index < locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have oldEq : locals[index] = old := List.getElem?_eq_some_iff.mp lookup |>.2
  have self : locals.set index old = locals := by
    rw [← oldEq]
    exact List.set_getElem_self bound
  have split := Code.encodeValues_set bound old
  rw [self] at split
  have offsetBound : Code.offset (locals.map Code.valueType) index ≤ (Code.encodeValues locals).length := by
    rw [Code.encodeValues_length]
    exact Code.offset_le _ _
  have length : ((Code.encodeValues locals).take (Code.offset (locals.map Code.valueType) index)).length =
      Code.offset (locals.map Code.valueType) index := by
    simp only [List.length_take, Nat.min_eq_left offsetBound]
  have region : WordsAt words base
      ((Code.encodeValues locals).take (Code.offset (locals.map Code.valueType) index) ++
      Code.encodeValue old ++
      ((Code.encodeValues locals).drop (Code.offset (locals.map Code.valueType) (index + 1)) ++ Code.encodeValues stack)) := by
    have full : WordsAt words base (Code.encodeValues locals ++ Code.encodeValues stack) := by
      simpa only [ValuesAt, Code.encodeValues_append] using live
    rw [split] at full
    simpa only [List.append_assoc] using full
  have widths : (Code.encodeValue replacement).length = (Code.encodeValue old).length := by
    simp only [Code.encodeValue_length, typed]
  have changed := WordsAt.copy_replace region input widths
    (by simpa only [length] using order)
    source (by simpa only [length] using destination)
  rw [length] at changed
  have updated := Code.encodeValues_set bound replacement
  simp only [ValuesAt, Code.encodeValues_append, updated]
  simpa only [List.append_assoc] using changed

end Itasca.Runtime.Interp

end

/-! ## Local Write -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- LOCAL_SET and LOCAL_TEE use the same concrete transfer. Only their live
operand-stack boundary differs; the source step derives from typed execution. -/
theorem dispatch_localWrite_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index src dst : U32) (keep : Bool)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (value old : val)
    (lookup : f.locals[index.val]? = some old)
    (compatible : Code.valueType value = Code.valueType old)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after,
      vals := front ++ [value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [value] })
    (source : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (destination : dst.val = Code.offset (f.locals.map Code.valueType) index.val) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (Code.move (Code.valueType value) dst src) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ ⦄ := by
  have typeLookup : (f.locals.map Code.valueType)[index.val]? = some (Code.valueType old) := by
    simpa using congrArg (Option.map Code.valueType) lookup
  have localEnd := Code.offset_add_width_le typeLookup
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + src.val) (Code.encodeValue value) := by
    simpa only [ValuesAt, source, Code.encodeValues, List.flatMap_cons, List.flatMap_nil, List.append_nil] using allValues.operands
  have nonempty : 0 < (Code.encodeValue value).length := by
    rw [Code.encodeValue_length]
    exact Code.width_positive _
  have sourceBound : raw.base.val + src.val + (Code.encodeValue value).length ≤ exec.slots.length := by
    have bound := (input ((Code.encodeValue value).length - 1) (by omega)).1
    change raw.base.val + src.val + ((Code.encodeValue value).length - 1) < exec.slots.length at bound
    omega
  have order : raw.base.val + dst.val + (Code.encodeValue value).length ≤ raw.base.val + src.val := by
    rw [Code.encodeValue_length, compatible, source, destination]
    simp only [List.map_append, Code.slots_append]
    omega
  have destinationBound : raw.base.val + dst.val + (Code.encodeValue value).length ≤ exec.slots.length := by omega
  have live : ValuesAt exec.slots.val raw.base.val
      (f.locals ++ (if keep then front ++ [value] else front)) := by
    cases keep with
    | false => exact allValues.locals
    | true => exact slots
  have changed := ValuesAt.copy_local live lookup compatible input
    (by rw [← destination]; exact Or.inl (by omega)) sourceBound
    (by simpa only [destination] using destinationBound)
  rw [← destination] at changed
  have type_eq (v : val) : Code.valueType v = Abs.valueType v := by
    cases v with
    | REF_NULL rt => cases rt <;> rfl
    | _ => rfl
  have compatible' : Abs.valueType value = Abs.valueType old := by
    simpa only [type_eq] using compatible
  have step : Abs.astep
      ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ := by
    cases keep <;> simp [Abs.astep, Abs.pop_append, lookup, compatible', Abs.advance]
  have simulation : Abs.NextSim
      ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
      ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ := by
    cases keep with
    | false =>
      exact Abs.instruction_simulation s ambient { f with vals := front ++ [value] } rest
        (.LOCAL_SET (.mk_uN index.val)) after _ (.local_set _) typed step
    | true =>
      exact Abs.instruction_simulation s ambient { f with vals := front ++ [value] } rest
        (.LOCAL_TEE (.mk_uN index.val)) after _ (.local_tee _) typed step
  apply WP.spec_mono (dispatch_move_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base (Code.valueType value) dst src
    (by simpa only [Code.encodeValue_length] using sourceBound)
    (by simpa only [Code.encodeValue_length] using destinationBound))
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  simp only [FrameSlots]
  rw [written]
  simpa only [Code.encodeValue_length] using changed

end Itasca.Runtime.Interp

end

/-! ## Local Code Point -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linearEmission_localGet_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (index : Nat) (h : Code.LinearEmission locals before (.LOCAL_GET (.mk_uN index)) emitted after) :
    ∃ ty localSlot stackSlot,
      locals[index]? = some ty ∧
      emitted = [Code.move ty stackSlot localSlot] ∧ after = before ++ [ty] ∧
      localSlot.val = Code.offset locals index ∧
      stackSlot.val = Code.slots locals + Code.slots before := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at h
  cases h with
  | localGet stack ty idx localSlot stackSlot hty hlocal hstack =>
    simp only [instr.LOCAL_GET.injEq, uN.mk_uN.injEq] at equality
    subst index
    exact ⟨ty, localSlot, stackSlot, hty, rfl, rfl, hlocal, hstack⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_localWrite_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (index : Nat) (keep : Bool)
    (h : Code.LinearEmission locals before
      (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    ∃ stack ty localSlot stackSlot,
      before = stack ++ [ty] ∧ locals[index]? = some ty ∧
      emitted = [Code.move ty localSlot stackSlot] ∧ after = (if keep then stack ++ [ty] else stack) ∧
      localSlot.val = Code.offset locals index ∧
      stackSlot.val = Code.slots locals + Code.slots stack := by
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
  | binary stack ity op left right hl hr => cases keep <;> cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases keep <;> simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => cases keep <;> simp_all

end Itasca.Runtime.Interp

end
