import Exec.Interp.Relations.ScalarDispatch
import Exec.Representation.Store
import Exec.Code.Local.Relations.Common.Rel

/-! Concrete slot and frame correspondences. These predicates describe data,
addresses, and emitted instruction locations; they contain no preservation or
simulation theorem as a premise. Structured program-counter certificates are
separate from the straight-line certificate available here. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A live contiguous region represents the given mathematical slot words.
Slots outside that region may contain dead operands or another frame. -/
def WordsAt (words : List U64) (base : Nat) (bits : List Nat) : Prop :=
  ∀ index, index < bits.length →
    base + index < words.length ∧ words[base + index]!.val = bits[index]!

def ValuesAt (words : List U64) (base : Nat) (values : List val) : Prop :=
  WordsAt words base (Code.encodeValues values)

def FrameSlots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) : Prop :=
  ValuesAt exec.slots.val raw.base.val (source.locals ++ source.vals)

/-- Resolve a concrete frame through the retained store, instance, function,
and signature tables, preserving actual owning-module bindings. -/
def FrameBinding {M : Type} (s : runtime.store.Store M) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) : Prop :=
  ∃ inst fn compiled signature,
    exec.store = s.id ∧ raw ∈ exec.frames.val ∧
    s.instances.val[raw.instance.val]? = some inst ∧
    s.funcs.val[source.fa]? = some fn ∧
    fn.code = .Wasm raw.instance raw.function ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    s.types.val[fn.signature.val]? = some signature ∧
    source.module = Store.decodeInstance s inst ∧
    source.resultTypes = signature.results.val.map sourceType ∧
    source.locals.map Code.valueType = compiled.locals.val.map sourceType ∧
    raw.base.val + compiled.slot_count.val ≤ exec.slots.length

/-- At a straight-line point, the source suffix and emitted bytecode fragment
agree at the actual program counter. Callers must separately establish this
certificate from the compiler; the relation does not presume that result. -/
def LinearPoint (raw : runtime.interp.Frame) (source : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (next : Nat) (output : List valtype) : Prop :=
  Code.LinearCodeRel (source.locals.map Code.valueType) (source.vals.map Code.valueType)
    source.code compiled.code.val raw.pc.val next output

theorem WordsAt.append_left {words : List U64} {base : Nat} {left right : List Nat}
    (h : WordsAt words base (left ++ right)) : WordsAt words base left := by
  intro index hi
  have hb : index < (left ++ right).length := by simp only [List.length_append]; omega
  obtain ⟨bound, value⟩ := h index hb
  refine ⟨bound, ?_⟩
  simpa only [_root_.getElem!_pos (left ++ right) index hb,
    _root_.getElem!_pos left index hi, List.getElem_append_left hi] using value

theorem WordsAt.append_right {words : List U64} {base : Nat} {left right : List Nat}
    (h : WordsAt words base (left ++ right)) : WordsAt words (base + left.length) right := by
  intro index hi
  have hb : left.length + index < (left ++ right).length := by simp only [List.length_append]; omega
  obtain ⟨bound, value⟩ := h (left.length + index) hb
  refine ⟨by simpa only [Nat.add_assoc] using bound, ?_⟩
  simpa only [_root_.getElem!_pos (left ++ right) (left.length + index) hb,
    _root_.getElem!_pos right index hi, List.getElem_append_right («as» := left) (bs := right) (i := left.length + index) (by omega),
    Nat.add_sub_cancel_left, Nat.add_assoc] using value

/-- A concrete point write performs the identical mathematical slot update. -/
theorem WordsAt.set {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (index : Nat) (word : U64) :
    WordsAt (words.set (base + index) word) base (bits.set index word.val) := by
  intro position hp
  have hp' : position < bits.length := by simpa only [List.length_set] using hp
  obtain ⟨bound, value⟩ := h position hp'
  have bound' : base + position < (words.set (base + index) word).length := by simpa only [List.length_set] using bound
  refine ⟨bound', ?_⟩
  rw [_root_.getElem!_pos (words.set (base + index) word) (base + position) bound', _root_.getElem!_pos (bits.set index word.val) position hp]
  by_cases same : index = position
  · subst position
    simp only [List.getElem_set_self]
  · have different : base + index ≠ base + position := by omega
    rw [List.getElem_set_ne different, List.getElem_set_ne same]
    simpa only [_root_.getElem!_pos words (base + position) bound,
      _root_.getElem!_pos bits position hp'] using value

/-- Binary operations overwrite their left operand and leave the old right
operand in a dead slot outside the new live region. -/
theorem WordsAt.binary_result {words : List U64} {base : Nat} {front : List Nat} {a b : Nat}
    (h : WordsAt words base (front ++ [a, b])) (value : U64) :
    WordsAt (words.set (base + front.length) value) base (front ++ [value.val]) := by
  have updated := h.set front.length value
  have exactUpdate : (front ++ [a, b]).set front.length value.val = front ++ [value.val, b] := by
    simp [List.set_append_right]
  rw [exactUpdate] at updated
  exact WordsAt.append_left (left := front ++ [value.val]) (right := [b]) (by
    simpa only [List.append_assoc, List.singleton_append] using updated)

theorem ValuesAt.locals {words : List U64} {base : Nat} {locals values : List val}
    (h : ValuesAt words base (locals ++ values)) : ValuesAt words base locals := by
  simp only [ValuesAt, Code.encodeValues_append] at h ⊢
  exact h.append_left

theorem ValuesAt.operands {words : List U64} {base : Nat} {locals values : List val}
    (h : ValuesAt words base (locals ++ values)) :
    ValuesAt words (base + Code.slots (locals.map Code.valueType)) values := by
  simp only [ValuesAt, Code.encodeValues_append] at h ⊢
  simpa only [Code.encodeValues_length] using h.append_right

/-- A concrete emitted instruction is fetched at its recorded code offset. -/
theorem emission_fetch {code : List Code.Bytecode} {pc : Nat}
    {head : Code.Bytecode} {emitted : List Code.Bytecode}
    (location : ∃ pre suffix, code = pre ++ head :: emitted ++ suffix ∧ pre.length = pc) :
    code[pc]? = some head := by
  obtain ⟨pre, suffix, rfl, rfl⟩ := location
  simp

/-- Split a checked emitted fragment at its source head. Zero-byte source
instructions retain the same program counter; nonempty emission exposes the
actual instruction fetched there. -/
theorem linearCodeRel_head {locals before after : List valtype} {source : List instr}
    {instruction : instr} {code : List Code.Bytecode} {pc next : Nat}
    (relation : Code.LinearCodeRel locals before (instruction :: source) code pc next after) :
    ∃ middle emitted,
      Code.LinearEmission locals before instruction emitted middle ∧
      (∀ head tail, emitted = head :: tail → code[pc]? = some head) ∧
      Code.LinearCodeRel locals middle source code (pc + emitted.length) next after := by
  obtain ⟨pre, full, suffix, hcode, hpc, hnext, relation⟩ := relation
  cases relation with
  | cons head tail =>
    rename_i middle emitted codeTail
    refine ⟨_, _, head, ?_, ?_⟩
    · intro first rest he
      apply emission_fetch (emitted := rest)
      refine ⟨pre, codeTail ++ suffix, ?_, hpc⟩
      rw [hcode, he]
      simp only [List.append_assoc, List.cons_append]
    · refine ⟨pre ++ emitted, codeTail, suffix, ?_, ?_, ?_, tail⟩
      · simpa only [List.append_assoc] using hcode
      · simp only [List.length_append, hpc]
      · simpa only [List.length_append, Nat.add_assoc] using hnext

end Exec.Interp
