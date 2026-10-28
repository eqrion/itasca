import Exec.Interp.Relations.LocalRegions
import Exec.Interp.Relations.Move
import Exec.Abs.Sim.Instruction

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
