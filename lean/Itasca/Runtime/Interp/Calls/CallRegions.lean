import Itasca.Runtime.Interp.Calls.Call
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Interp.Relations.Defaults

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
  apply h.congr_region (zeroWords_length _ _ _)
  intro j hj
  exact (zeroWords_effect words start count bound).2 _ (by omega)

theorem zeroWords_represents (words : List U64) (start count : Nat)
    (bound : start + count ≤ words.length) :
    WordsAt (zeroWords words start count) start (List.replicate count 0) := by
  intro j hj
  have hj' : j < count := by simpa only [List.length_replicate] using hj
  have word := (zeroWords_effect words start count bound).1 j hj'
  have valid : start + j < (zeroWords words start count).length := by rw [zeroWords_length]; omega
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
    (parameters : code.param_slots.val = Code.slots (args.map Code.valueType))
    (locals : code.local_slots.val = code.param_slots.val + Code.slots localTypes)
    (capacity : code.local_slots.val ≤ code.slot_count.val)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    ValuesAt after.slots.val base.val (args ++ defaults) := by
  obtain ⟨_, slots, _⟩ := effect
  have bound : base.val + code.param_slots.val + Code.slots localTypes ≤
      (before.slots.val ++ List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64).length := by
    simp only [List.length_append, List.length_replicate]
    change base.val + code.param_slots.val + Code.slots localTypes ≤
      before.slots.length + (base.val + code.slot_count.val - before.slots.length)
    omega
  have initialized := zeroWords_represents
    (before.slots.val ++ List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64)
    (base.val + code.param_slots.val) (Code.slots localTypes) bound
  have saved := (WordsAt.extend arguments
    (List.replicate (base.val + code.slot_count.val - before.slots.length) 0#u64)).zero_preserves
    (base.val + code.param_slots.val) (Code.slots localTypes) bound
    (Or.inl (by rw [Code.encodeValues_length, parameters]))
  have full := WordsAt.append saved (by simpa only [Code.encodeValues_length, parameters] using initialized)
  simp only [ValuesAt, Code.encodeValues_append, encode_defaultLocals localTypes defaults default]
  rw [slots]
  have count : code.local_slots.val - code.param_slots.val = Code.slots localTypes := by omega
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
