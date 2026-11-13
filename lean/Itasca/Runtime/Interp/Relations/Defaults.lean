import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Numeric.Integer.Int
import Itasca.Runtime.Interp.Numeric.Float
import Itasca.Runtime.Compiler.Local.Relations.Emission.Rel
import Itasca.Runtime.Platform.Laws

/-!
Sections, each formerly its own module: DecodeValue, ScalarDispatch, Execute, Copy, Rel, CopyRel, Ensure, Fetch, InitLocals, Defaults.
-/

/-! ## DecodeValue -/

section

/-! Primitive result decoding, independent of structural store invariants. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
open Itasca.Runtime.Store

theorem cast_usize_exact (n : U64) (h : n.val ≤ Usize.max) :
    (UScalar.cast .Usize n).val = n.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have hp : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp only [Usize.max, UScalarTy.numBits, Usize.numBits] at *
  omega

theorem decode_words_code (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (hfloat : ty = .F32 → lo.val < 2^32) :
    Compiler.decodeOne (Interp.sourceType ty) (Interp.pairWords ty (lo, hi)) =
      some (decodeWords ty lo hi, []) := by
  cases ty <;> simp only [Interp.sourceType, Interp.pairWords, Compiler.decodeOne, decodeWords,
    decodeRef, decodeElemType, refVal]
  all_goals simp
  case F32 =>
    have hb : lo.val < 4294967296 := hfloat rfl
    rw [Nat.mod_eq_of_lt hb]
  case FuncRef => split <;> rfl
  case ExternRef => split <;> rfl


/-- The actual word decoder returns the value observed by decodeStore. The only
extra bound is on non-null reference encodings, supplied by ReferenceShape. -/
theorem decode_value_boundary (ty : Itasca.wasm_types.ValueType) (lo hi : U64) (store : Usize)
    (href : ty = .FuncRef ∨ ty = .ExternRef → lo.val ≤ Usize.max) :
    runtime.value.decode ty lo hi store ⦃ value =>
      Interp.rawType value = ty ∧ Interp.sourceValue value = decodeWords ty lo hi ⦄ := by
  cases ty <;> simp only [runtime.value.decode, decodeWords]
  all_goals simp [lift, Interp.rawType, Interp.sourceValue]
  case V128 =>
    step as ⟨shifted, hshifted⟩
    congr 2
    have hlow : lo.val < 2^64 := by scalar_tac
    have hhigh : hi.val * 2^64 < 2^128 := by scalar_tac
    have hl128 : lo.val < 2^128 := by scalar_tac
    have hh128 : hi.val < 2^128 := by scalar_tac
    simp only [UScalar.val_or, hshifted, UScalar.cast_val_eq, UScalarTy.numBits]
    rw [Nat.mod_eq_of_lt hl128, Nat.mod_eq_of_lt hh128]
    simp only [U128.size, U128.numBits, UScalarTy.numBits]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhigh]
    rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq]
    omega
  case FuncRef =>
    split
    · rename_i hz
      simp [hz, decodeRef, decodeElemType, refVal]
    · rename_i hn
      have hbound := href (Or.inl rfl)
      have hcast := cast_usize_exact lo hbound
      step as ⟨index, hindex⟩
      simp [decodeRef, decodeElemType, refVal, show lo.val ≠ 0 by scalar_tac]
      scalar_tac
  case ExternRef =>
    split
    · rename_i hz
      simp [hz, decodeRef, decodeElemType, refVal]
    · rename_i hn
      have hbound := href (Or.inr rfl)
      have hcast := cast_usize_exact lo hbound
      step as ⟨index, hindex⟩
      simp [decodeRef, decodeElemType, refVal, show lo.val ≠ 0 by scalar_tac]
      scalar_tac



/-- The extracted primitive decoder recovers any well-formed source value
represented by its exact typed word pair. -/
theorem decode_value_represents (ty : Itasca.wasm_types.ValueType) (lo hi : U64) (store : Usize)
    (value : val) (wellFormed : wf_val value)
    (typed : sourceType ty = Compiler.valueType value)
    (represented : pairWords ty (lo, hi) = Compiler.encodeValue value)
    (floatBound : ty = .F32 → lo.val < 2^32)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → lo.val ≤ Usize.max) :
    runtime.value.decode ty lo hi store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  have roundtrip := Compiler.decode_encode value wellFormed []
  simp only [List.append_nil] at roundtrip
  rw [← typed, ← represented, decode_words_code ty lo hi floatBound] at roundtrip
  have decoded : decodeWords ty lo hi = value := congrArg Prod.fst (Option.some.inj roundtrip)
  step with decode_value_boundary ty lo hi store referenceBound as ⟨result, hty, hvalue⟩
  exact ⟨hty, hvalue.trans decoded⟩

end Itasca.Runtime.Interp

end

/-! ## ScalarDispatch -/

section

/-! The scalar dispatch boundary reads both operands before writing the result.
A numeric trap leaves the complete execution state unchanged. These lemmas
connect the separately checked opcode handlers to their actual slot mutations. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Every field other than slot contents is preserved. -/
def SlotsEffect (before after : runtime.interp.Execution) (words : List U64) : Prop :=
  after.slots.val = words ∧ { after with slots := before.slots } = before

def ScalarEffect (before : runtime.interp.Execution) (position : Nat)
    (numeric : core.result.Result U64 runtime.ExecError)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match numeric with
  | .Ok value => out.1 = .Ok () ∧ SlotsEffect before out.2 (before.slots.val.set position value)
  | .Err error => out = (.Err error, before)

theorem execute_scalar_effect {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : U16) (dst a b : U32)
    (ha : base.val + a.val < exec.slots.length)
    (hb : base.val + b.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length)
    (numeric : core.result.Result U64 runtime.ExecError)
    (hn : runtime.interp.int.scalar ops op
      exec.slots.val[base.val + a.val]! exec.slots.val[base.val + b.val]! = .ok numeric) :
    runtime.interp.execute_scalar ops exec base op dst a b ⦃ out =>
      ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  unfold runtime.interp.execute_scalar
  simp only [lift, bind_ok]
  step as ⟨pa, hpa⟩
  step as ⟨va, hva⟩
  step as ⟨pb, hpb⟩
  step as ⟨vb, hvb⟩
  have ha' : base.val + a.val < exec.slots.val.length := ha
  have hb' : base.val + b.val < exec.slots.val.length := hb
  have hva' : va = exec.slots.val[base.val + a.val]! := by
    rw [_root_.getElem!_pos exec.slots.val (base.val + a.val) ha']
    simpa only [hpa, U32.cast_Usize_val_eq] using hva
  have hvb' : vb = exec.slots.val[base.val + b.val]! := by
    rw [_root_.getElem!_pos exec.slots.val (base.val + b.val) hb']
    simpa only [hpb, U32.cast_Usize_val_eq] using hvb
  rw [hva', hvb', hn]
  cases numeric <;> step* <;> simp_all [ScalarEffect, SlotsEffect]

end Itasca.Runtime.Interp

end

/-! ## Execute -/

section

/-! Exact state effects of the extracted copy, constant, and jump handlers.
Bounds are slot/frame bounds, independent of compiler correctness. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (platform : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (alloc : runtime.platform.Alloc A)

@[step] theorem const32_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst value : U32)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_const32 exec base dst value
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val) (UScalar.cast .U64 value)) ⦄ := by
  unfold runtime.interp.execute_const32
  step* <;> simp_all [SlotsEffect]

@[step] theorem const64_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst : U32) (value : U64)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_const64 exec base dst value
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val) value) ⦄ := by
  unfold runtime.interp.execute_const64
  step* <;> simp_all [SlotsEffect]

@[step] theorem copy_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src : U32)
    (hs : base.val + src.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_copy exec base dst src
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val)
          exec.slots.val[base.val + src.val]!) ⦄ := by
  unfold runtime.interp.execute_copy
  step* <;> simp_all [SlotsEffect, _root_.getElem!_pos]

/-- A jump changes only the selected frame's program counter. -/
def JumpEffect (before after : runtime.interp.Execution) (index : Nat) (target : U32) : Prop :=
  ∃ frame, before.frames.val[index]? = some frame ∧
    after.frames.val = before.frames.val.set index { frame with pc := target } ∧
    { after with frames := before.frames } = before

@[step] theorem jump_effect (exec : runtime.interp.Execution)
    (index : Usize) (target : U32) (hi : index.val < exec.frames.length) :
    runtime.interp.execute_jump exec index target
      ⦃ out => out.1 = .Ok () ∧ JumpEffect exec out.2 index.val target ⦄ := by
  unfold runtime.interp.execute_jump
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

@[step] theorem jump_if_zero_effect (exec : runtime.interp.Execution)
    (index base : Usize) (cond target : U32)
    (hi : index.val < exec.frames.length)
    (hc : base.val + cond.val < exec.slots.length) :
    runtime.interp.execute_jump_if_zero exec index base cond target
      ⦃ out => out.1 = .Ok () ∧
        if UScalar.cast .U32 exec.slots.val[base.val + cond.val]! = 0#u32
        then JumpEffect exec out.2 index.val target else out.2 = exec ⦄ := by
  unfold runtime.interp.execute_jump_if_zero
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

@[step] theorem jump_if_non_zero_effect (exec : runtime.interp.Execution)
    (index base : Usize) (cond target : U32)
    (hi : index.val < exec.frames.length)
    (hc : base.val + cond.val < exec.slots.length) :
    runtime.interp.execute_jump_if_non_zero exec index base cond target
      ⦃ out => out.1 = .Ok () ∧
        if UScalar.cast .U32 exec.slots.val[base.val + cond.val]! = 0#u32
        then out.2 = exec else JumpEffect exec out.2 index.val target ⦄ := by
  unfold runtime.interp.execute_jump_if_non_zero
  step* <;> simp_all [JumpEffect, _root_.getElem!_pos]

end Itasca.Runtime.Interp

end

/-! ## Copy -/

section

/-! The interpreter copies slots from low to high. The mathematical operation
retains that order, including the behavior of overlapping source/destination
ranges. Branch and return proofs additionally establish downward movement. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def copyWords (words : List U64) (dst src : Nat) : Nat → List U64
  | 0 => words
  | n + 1 => copyWords (words.set dst words[src]!) (dst + 1) (src + 1) n

theorem copy_words_length (words : List U64) (dst src n : Nat) :
    (copyWords words dst src n).length = words.length := by
  induction n generalizing words dst src with
  | zero => rfl
  | succ n ih => simp only [copyWords, ih, List.length_set]

@[step] theorem copy_loop_effect (words : Slice U64) (dst src n i : Usize)
    (hs : src.val + n.val ≤ words.length)
    (hd : dst.val + n.val ≤ words.length)
    (hi : i.val ≤ n.val) :
    runtime.interp.copy_loop words dst src n i ⦃ out =>
      out.val = copyWords words.val (dst.val + i.val) (src.val + i.val) (n.val - i.val) ⦄ := by
  unfold runtime.interp.copy_loop
  apply loop.spec_decr_nat (fun p => n.val - p.2.val)
    (fun p => p.2.val ≤ n.val ∧ p.1.length = words.length ∧
      copyWords p.1.val (dst.val + p.2.val) (src.val + p.2.val) (n.val - p.2.val) =
        copyWords words.val (dst.val + i.val) (src.val + i.val) (n.val - i.val))
  · rintro ⟨current, j⟩ ⟨hj, hlen, hcopy⟩
    dsimp only at hj hlen hcopy
    unfold runtime.interp.copy_loop.body
    dsimp only
    split
    · rename_i hmore
      have hlt : j.val < n.val := by scalar_tac
      step as ⟨readPos, hreadPos⟩
      step as ⟨value, hvalue⟩
      step as ⟨writePos, hwritePos⟩
      step as ⟨updated, hupdated⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simpa [hupdated] using hlen
      · have hremaining : n.val - j.val = (n.val - next.val) + 1 := by omega
        rw [hremaining, copyWords] at hcopy
        simp only [hupdated, Slice.set_val_eq, hwritePos, hnext]
        have hv : value = current.val[src.val + j.val]! := by
          have hb : src.val + j.val < current.val.length := by change src.val + j.val < current.length; omega
          rw [_root_.getElem!_pos current.val _ hb]
          simpa [hreadPos] using hvalue
        simpa [hv, hnext, Nat.add_assoc] using hcopy
      · omega
    · have heq : j.val = n.val := by scalar_tac
      simpa [heq, copyWords] using hcopy
  · exact ⟨hi, rfl, rfl⟩

@[step] theorem copy_effect_words (words : Slice U64) (dst src n : Usize)
    (hs : src.val + n.val ≤ words.length)
    (hd : dst.val + n.val ≤ words.length) :
    runtime.interp.copy words dst src n ⦃ out =>
      out.val = copyWords words.val dst.val src.val n.val ⦄ := by
  simpa [runtime.interp.copy] using copy_loop_effect words dst src n 0#usize hs hd (by simp)

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (platform : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

@[step] theorem copy_n_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src n : U32)
    (hs : base.val + src.val + n.val ≤ exec.slots.length)
    (hd : base.val + dst.val + n.val ≤ exec.slots.length)
    (hsrc : base.val + src.val ≤ Usize.max)
    (hdst : base.val + dst.val ≤ Usize.max) :
    runtime.interp.execute_copy_n exec base dst src n
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) n.val) ⦄ := by
  unfold runtime.interp.execute_copy_n
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect] <;> first | assumption | omega

@[step] theorem copy2_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src : U32)
    (hs : base.val + src.val + 2 ≤ exec.slots.length)
    (hd : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_copy2 exec base dst src
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) 2) ⦄ := by
  unfold runtime.interp.execute_copy2
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect] <;> first | assumption | omega

/-- Returning copies the declared result words to the caller's destination and
removes exactly the last concrete frame. -/
def ReturnEffect (before after : runtime.interp.Execution) (base src n : Nat) : Prop :=
  after.slots.val = copyWords before.slots.val base (base + src) n ∧
  after.frames.val = before.frames.val.dropLast ∧
  { after with slots := before.slots, frames := before.frames } = before

@[step] theorem return_effect (exec : runtime.interp.Execution)
    (base : Usize) (src n : U32)
    (hs : base.val + src.val + n.val ≤ exec.slots.length)
    (hsrc : base.val + src.val ≤ Usize.max) :
    runtime.interp.execute_return exec base src n
      ⦃ out => out.1 = .Ok () ∧ ReturnEffect exec out.2 base.val src.val n.val ⦄ := by
  have hd : base.val + n.val ≤ exec.slots.slice.length := by
    change base.val + n.val ≤ exec.slots.length
    omega
  unfold runtime.interp.execute_return
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [alloc.vec.Vec.pop, ReturnEffect] <;> first | assumption | omega

end Itasca.Runtime.Interp

end

/-! ## Rel -/

section

/-! Concrete slot and frame correspondences. These predicates describe data,
addresses, and emitted instruction locations; they contain no preservation or
simulation theorem as a premise. Structured program-counter certificates are
separate from the straight-line certificate available here. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A live contiguous region represents the given mathematical slot words.
Slots outside that region may contain dead operands or another frame. -/
def WordsAt (words : List U64) (base : Nat) (bits : List Nat) : Prop :=
  ∀ index, index < bits.length →
    base + index < words.length ∧ words[base + index]!.val = bits[index]!

def ValuesAt (words : List U64) (base : Nat) (values : List val) : Prop :=
  WordsAt words base (Compiler.encodeValues values)

def FrameSlots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) : Prop :=
  ValuesAt exec.slots.val raw.base.val (source.locals ++ source.vals)

/-- Resolve a concrete frame through the retained store, instance, function,
and signature tables, preserving actual owning-module bindings. -/
def FrameBinding {M : Type} (s : runtime.store.Store M) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) : Prop :=
  ∃ inst fn compiled signature,
    exec.store = s.id ∧ raw ∈ exec.frames.val ∧
    s.instances.val[raw.instance.val]? = some inst ∧
    s.funcs.val[source.fa]? = some fn ∧
    fn.code = .Wasm raw.instance raw.function ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    s.types.val[fn.signature.val]? = some signature ∧
    source.module = Store.decodeInstance s inst ∧
    source.resultTypes = signature.results.val.map sourceType ∧
    source.locals.map Compiler.valueType = compiled.locals.val.map sourceType ∧
    raw.base.val + compiled.slot_count.val ≤ exec.slots.length

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
  simp only [ValuesAt, Compiler.encode_values_append] at h ⊢
  exact h.append_left

theorem ValuesAt.operands {words : List U64} {base : Nat} {locals values : List val}
    (h : ValuesAt words base (locals ++ values)) :
    ValuesAt words (base + Compiler.slots (locals.map Compiler.valueType)) values := by
  simp only [ValuesAt, Compiler.encode_values_append] at h ⊢
  simpa only [Compiler.encode_values_length] using h.append_right

end Itasca.Runtime.Interp

end

/-! ## CopyRel -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Forward copies read the original source when moving downward or into a
disjoint higher region. Both cases occur in locals, branches and calls. -/
theorem copy_words_safe (words : List U64) (dst src n : Nat)
    (order : dst ≤ src ∨ src + n ≤ dst)
    (source : src + n ≤ words.length) (destination : dst + n ≤ words.length) :
    (∀ j, j < n → (copyWords words dst src n)[dst + j]? = words[src + j]?) ∧
    (∀ j, j < dst ∨ dst + n ≤ j → (copyWords words dst src n)[j]? = words[j]?) := by
  induction n generalizing words dst src with
  | zero => simp [copyWords]
  | succ n ih =>
    have hs : src < words.length := by omega
    have hd : dst < words.length := by omega
    have hnext := ih (words.set dst words[src]!) (dst + 1) (src + 1)
      (by omega) (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
    simp only [copyWords]
    constructor
    · intro j hj
      cases j with
      | zero =>
        have hset : (words.set dst words[src]!)[dst]? = words[src]? := by simp [hd, hs]
        simpa using (hnext.2 dst (Or.inl (by omega))).trans hset
      | succ j =>
        have hjn : j < n := by omega
        have he : dst + (j + 1) = dst + 1 + j := by omega
        rw [he, hnext.1 j hjn]
        have hne : dst ≠ src + 1 + j := by omega
        simp only [List.getElem?_set, hne, if_false]
        congr 1 <;> omega
    · intro j hj
      rw [hnext.2 j (by omega)]
      have hne : j ≠ dst := by omega
      simp [List.getElem?_set, hne]

/-- A bounded live region survives a change that preserves its indexed words. -/
theorem WordsAt.congr_region {before after : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt before base bits) (length : after.length = before.length)
    (same : ∀ j, j < bits.length → after[base + j]? = before[base + j]?) :
    WordsAt after base bits := by
  intro j hj
  obtain ⟨bound, value⟩ := h j hj
  have bound' : base + j < after.length := by omega
  have he := same j hj
  rw [List.getElem?_eq_getElem bound', List.getElem?_eq_getElem bound] at he
  have wordEq := Option.some.inj he
  refine ⟨bound', ?_⟩
  rw [_root_.getElem!_pos after (base + j) bound', wordEq]
  simpa only [_root_.getElem!_pos before (base + j) bound] using value

/-- Copy a live mathematical word region, including overlapping downward moves. -/
theorem WordsAt.copy {words : List U64} {src : Nat} {bits : List Nat}
    (h : WordsAt words src bits) (dst : Nat)
    (order : dst ≤ src ∨ src + bits.length ≤ dst)
    (destination : dst + bits.length ≤ words.length) :
    WordsAt (copyWords words dst src bits.length) dst bits := by
  cases bits with
  | nil => intro j hj; simp at hj
  | cons bit bits =>
    have source : src + (bit :: bits).length ≤ words.length := by
      have last := (h bits.length (by simp)).1
      simp only [List.length_cons] at *
      omega
    have effect := copy_words_safe words dst src (bit :: bits).length order source destination
    intro j hj
    obtain ⟨sourceBound, value⟩ := h j hj
    have bound : dst + j < (copyWords words dst src (bit :: bits).length).length := by
      rw [copy_words_length]
      omega
    have same := effect.1 j hj
    rw [List.getElem?_eq_getElem bound, List.getElem?_eq_getElem sourceBound] at same
    refine ⟨bound, ?_⟩
    rw [_root_.getElem!_pos (copyWords words dst src (bit :: bits).length) (dst + j) bound, Option.some.inj same]
    simpa only [_root_.getElem!_pos words (src + j) sourceBound] using value

/-- A copy preserves every live region disjoint from its destination. -/
theorem WordsAt.copy_preserves {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (dst src n : Nat)
    (order : dst ≤ src ∨ src + n ≤ dst)
    (source : src + n ≤ words.length) (destination : dst + n ≤ words.length)
    (outside : ∀ j, j < bits.length → base + j < dst ∨ dst + n ≤ base + j) :
    WordsAt (copyWords words dst src n) base bits := by
  apply h.congr_region (copy_words_length words dst src n)
  intro j hj
  exact (copy_words_safe words dst src n order source destination).2 _ (outside j hj)

/-- Adjacent represented regions compose into one live region. -/
theorem WordsAt.append {words : List U64} {base : Nat} {left right : List Nat}
    (first : WordsAt words base left) (second : WordsAt words (base + left.length) right) :
    WordsAt words base (left ++ right) := by
  intro j hj
  by_cases inside : j < left.length
  · obtain ⟨bound, value⟩ := first j inside
    refine ⟨bound, ?_⟩
    simpa only [_root_.getElem!_pos (left ++ right) j hj,
      List.getElem_append_left inside, _root_.getElem!_pos left j inside] using value
  · have rightBound : j - left.length < right.length := by
      simp only [List.length_append] at hj
      omega
    obtain ⟨bound, value⟩ := second (j - left.length) rightBound
    have position : base + left.length + (j - left.length) = base + j := by omega
    rw [position] at bound value
    refine ⟨bound, ?_⟩
    simpa only [_root_.getElem!_pos (left ++ right) j hj,
      List.getElem_append_right (by omega : left.length ≤ j),
      _root_.getElem!_pos right (j - left.length) rightBound] using value

/-- Appending a copied value retains all earlier live slots. This covers the
local.get transfer once the local's encoded source region is resolved. -/
theorem WordsAt.copy_append {words : List U64} {base src : Nat} {front value : List Nat}
    (live : WordsAt words base front) (input : WordsAt words src value)
    (order : base + front.length ≤ src ∨ src + value.length ≤ base + front.length)
    (source : src + value.length ≤ words.length)
    (destination : base + front.length + value.length ≤ words.length) :
    WordsAt (copyWords words (base + front.length) src value.length) base (front ++ value) := by
  apply WordsAt.append
  · apply live.copy_preserves (base + front.length) src value.length order source destination
    intro j hj
    exact Or.inl (by omega)
  · exact input.copy (base + front.length) order destination

end Itasca.Runtime.Interp

end

/-! ## Ensure -/

section

/-! Slot storage growth returns normally under the allocator law. Its only
rejections are the requested value limit and an actual allocator rejection. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem ensure_loop_effect (before : alloc.vec.Vec U64) (bound : Usize)
    (fits : before.length ≤ bound.val) :
    runtime.interp.Execution.ensure_loop before bound ⦃ after =>
      after.val = before.val ++ List.replicate (bound.val - before.length) 0#u64 ⦄ := by
  unfold runtime.interp.Execution.ensure_loop
  apply loop.spec_decr_nat (fun current => bound.val - current.length)
    (fun current => current.length ≤ bound.val ∧
      current.val ++ List.replicate (bound.val - current.length) 0#u64 =
        before.val ++ List.replicate (bound.val - before.length) 0#u64)
  · intro current hinv
    obtain ⟨hlen, hwords⟩ := hinv
    unfold runtime.interp.Execution.ensure_loop.body
    dsimp only
    split
    · have hlt : current.length < bound.val := by scalar_tac
      have hpush : current.length < Usize.max := by scalar_tac
      step as ⟨after, happend⟩
      have hlength : after.length = current.length + 1 := by simp [happend]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · rw [happend, List.append_assoc]
        have hremaining : bound.val - current.length = (bound.val - after.length) + 1 := by omega
        rw [hremaining] at hwords
        simpa [List.replicate_succ] using hwords
      · omega
    · have heq : current.length = bound.val := by scalar_tac
      simpa [heq] using hwords
  · exact ⟨fits, rfl⟩

def EnsureEffect {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.interp.Execution) (bound limit : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match out.1 with
  | .Ok _ => bound.val ≤ limit.val ∧ SlotsEffect before out.2
      (before.slots.val ++ List.replicate (bound.val - before.slots.length) 0#u64)
  | .Err (.Exhausted .Values) => limit.val < bound.val ∧ out.2 = before
  | .Err (.Exhausted .Allocation) =>
      bound.val ≤ limit.val ∧ before.slots.length < bound.val ∧ out.2 = before ∧
      ∃ n : Usize, n.val = bound.val - before.slots.length ∧
        allocator.reserve before.slots n = .ok (false, before.slots)
  | .Err _ => False

@[step] theorem ensure_effect {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (before : runtime.interp.Execution)
    (bound limit : Usize) :
    runtime.interp.Execution.ensure allocator before bound limit
      ⦃ out => EnsureEffect allocator before bound limit out ⦄ := by
  unfold runtime.interp.Execution.ensure
  split
  · simp only [WP.spec_ok, EnsureEffect]
    exact ⟨by scalar_tac, trivial⟩
  · rename_i within
    dsimp only
    split
    · rename_i grow
      step as ⟨n, hn⟩
      obtain ⟨answer, hreserve⟩ := law.reserve_eq before.slots n
      unfold runtime.reserve
      rw [hreserve, bind_ok]
      cases answer with
      | false =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          EnsureEffect]
        exact ⟨by scalar_tac, by scalar_tac, n, hn, hreserve⟩
      | true =>
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step with ensure_loop_effect before.slots bound (by scalar_tac) as ⟨after, hafter⟩
        exact ⟨by scalar_tac, hafter, rfl⟩
    · have hbound : bound.val ≤ before.slots.length := by scalar_tac
      simp [EnsureEffect, SlotsEffect, Nat.sub_eq_zero_of_le hbound]
      scalar_tac

end Itasca.Runtime.Interp

end

/-! ## Fetch -/

section

/-! Fetching an instruction in the extracted interpreter. The compiler/frame
relation supplies address and program-counter bounds; the selected handler
supplies its own postcondition. This bridge checks all intervening indexing and
the exact program-counter update. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem vec_index_given {T : Type} (values : alloc.vec.Vec T)
    (index : Usize) (value : T) (h : values.val[index.val]? = some value) :
    alloc.vec.Vec.index_usize values index
      ⦃ out => out = value ⦄ := by
  have hi : index.val < values.length := List.getElem?_eq_some_iff.mp h |>.1
  step as ⟨out, hout⟩
  have he := List.getElem?_eq_getElem hi
  rw [h] at he
  exact hout.trans (Option.some.inj he).symm

theorem step_fetch_div {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some inst)
    (hc : inst.module.functions.val[frame.function.val]? = some code)
    (hop : code.code.val[frame.pc.val]? = some instruction)
    (pcBound : frame.pc.val < U32.max)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (handler : ∀ next : U32, next.val = frame.pc.val + 1 →
      DivSpec cause (runtime.interp.dispatch memory hooks floats allocator
        { exec with frames := exec.frames.set index { frame with pc := next } }
        store platform index frame.instance frame.function frame.base instruction) post) :
    DivSpec cause (runtime.interp.step memory hooks floats allocator exec store platform) post := by
  unfold runtime.interp.step
  step as ⟨actualIndex, hindex⟩
  have he : actualIndex = index := by scalar_tac
  subst actualIndex
  step with vec_index_given exec.frames index frame hf as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.instances frame.instance inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions frame.function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given code.code (UScalar.cast .Usize frame.pc) instruction
    (by simpa only [U32.cast_Usize_val_eq] using hop) as ⟨found, hfound⟩
  subst found
  have hchecked := U32.checked_add_bv_spec frame.pc 1#u32
  cases hnext : U32.checked_add frame.pc 1#u32 with
  | none =>
    simp only [hnext] at hchecked
    scalar_tac
  | some next =>
    simp only [hnext] at hchecked ⊢
    step as ⟨old, back, hold, hback⟩
    have hframe : old = frame := by
      have he := List.getElem?_eq_getElem (show index.val < exec.frames.length by omega)
      rw [hf] at he
      exact hold.trans (Option.some.inj he).symm
    have hb : index.val < exec.frames.val.length := by
      change index.val < exec.frames.length
      omega
    have hread : exec.frames.val[index.val]'hb = frame := hold.symm.trans hframe
    simpa only [hback, hframe, hread] using handler next hchecked.2.1

theorem step_fetch {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some inst)
    (hc : inst.module.functions.val[frame.function.val]? = some code)
    (hop : code.code.val[frame.pc.val]? = some instruction)
    (pcBound : frame.pc.val < U32.max)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (handler : ∀ next : U32, next.val = frame.pc.val + 1 →
      runtime.interp.dispatch memory hooks floats allocator
        { exec with frames := exec.frames.set index { frame with pc := next } }
        store platform index frame.instance frame.function frame.base instruction ⦃ post ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ post ⦄ :=
  (step_fetch_div memory hooks floats allocator exec store platform index frame inst code instruction
    last hf hi hc hop pcBound False post fun next hnext => .of_spec _ _ _ _ (handler next hnext)).spec

end Itasca.Runtime.Interp

end

/-! ## InitLocals -/

section

/-! Function entry clears precisely the non-parameter local words. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def zeroWords (words : List U64) (start : Nat) : Nat → List U64
  | 0 => words
  | n + 1 => zeroWords (words.set start 0#u64) (start + 1) n

theorem zero_words_length (words : List U64) (start n : Nat) :
    (zeroWords words start n).length = words.length := by
  induction n generalizing words start with
  | zero => rfl
  | succ n ih => simp only [zeroWords, ih, List.length_set]

theorem zero_words_effect (words : List U64) (start n : Nat)
    (bound : start + n ≤ words.length) :
    (∀ j, j < n → (zeroWords words start n)[start + j]? = some 0#u64) ∧
    (∀ j, j < start ∨ start + n ≤ j → (zeroWords words start n)[j]? = words[j]?) := by
  induction n generalizing words start with
  | zero => simp [zeroWords]
  | succ n ih =>
    have hs : start < words.length := by omega
    have hnext := ih (words.set start 0#u64) (start + 1)
      (by simp only [List.length_set]; omega)
    simp only [zeroWords]
    constructor
    · intro j hj
      cases j with
      | zero =>
        have hset : (words.set start 0#u64)[start]? = some 0#u64 := by simp [hs]
        simpa using (hnext.2 start (Or.inl (by omega))).trans hset
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using hnext.1 j (by omega)
    · intro j hj
      rw [hnext.2 j (by omega)]
      have hne : j ≠ start := by omega
      simp [hne]

@[step] theorem init_locals_effect (exec : runtime.interp.Execution)
    (base : Usize) (locals : U32) (start : Usize)
    (bound : base.val + locals.val ≤ exec.slots.length)
    (range : start.val ≤ base.val + locals.val) :
    runtime.interp.call_loop3 exec base locals start ⦃ out => SlotsEffect exec out
      (zeroWords exec.slots.val start.val (base.val + locals.val - start.val)) ⦄ := by
  unfold runtime.interp.call_loop3
  apply loop.spec_decr_nat (fun p => base.val + locals.val - p.2.val)
    (fun p => p.2.val ≤ base.val + locals.val ∧
      p.1.slots.length = exec.slots.length ∧
      { p.1 with slots := exec.slots } = exec ∧
      zeroWords p.1.slots.val p.2.val (base.val + locals.val - p.2.val) =
        zeroWords exec.slots.val start.val (base.val + locals.val - start.val))
  · rintro ⟨current, index⟩ ⟨hindex, hlen, hrest, hwords⟩
    dsimp only at hindex hlen hrest hwords
    unfold runtime.interp.call_loop3.body
    simp only [lift, bind_ok]
    step as ⟨last, hlast⟩
    split
    · have hlt : index.val < base.val + locals.val := by scalar_tac
      step as ⟨old, back, hold, hback⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simp [hback, hlen]
      · simpa using hrest
      · have hn : base.val + locals.val - index.val =
            (base.val + locals.val - next.val) + 1 := by omega
        rw [hn, zeroWords] at hwords
        simpa [hback, hnext] using hwords
      · omega
    · have heq : index.val = base.val + locals.val := by scalar_tac
      exact ⟨by simpa [heq, zeroWords] using hwords, hrest⟩
  · exact ⟨range, rfl, rfl, rfl⟩

end Itasca.Runtime.Interp

end

/-! ## Defaults -/

section

namespace Itasca.Runtime.Interp

theorem encode_default_value {ty : valtype} {value : val}
    (default : SourceMachine.defaultValue ty = some value) :
    Compiler.encodeValue value = List.replicate (Compiler.width ty) 0 := by
  cases ty <;> simp only [SourceMachine.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals simp [SourceMachine.integerVal, Compiler.encodeValue, Compiler.width,
    SpecExt.Builtins.floatBits, SpecExt.Builtins.magnitudeBits, List.replicate]


/-- The abstract defaults occupy exactly the zero words written by the real
callee initializer, including float +0, null references, and both vector slots. -/
theorem encode_default_locals (types : List valtype) (values : List val)
    (defaults : SourceMachine.defaultLocals (types.map local.LOCAL) = some values) :
    Compiler.encodeValues values = List.replicate (Compiler.slots types) 0 := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, SourceMachine.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : SourceMachine.defaultValue ty with
    | none => simp [SourceMachine.defaultLocals, hv] at defaults
    | some value =>
      cases ht : SourceMachine.defaultLocals (types.map local.LOCAL) with
      | none => simp [SourceMachine.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [SourceMachine.defaultLocals, hv, ht] at defaults
        subst values
        change Compiler.encodeValue value ++ Compiler.encodeValues tail = List.replicate (Compiler.width ty + Compiler.slots types) 0
        rw [encode_default_value hv, ih tail ht, List.replicate_add]


theorem default_value_type {ty : valtype} {value : val}
    (default : SourceMachine.defaultValue ty = some value) : Compiler.valueType value = ty := by
  cases ty <;> simp only [SourceMachine.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals rfl

/-- Default construction preserves the declared local type sequence exactly. -/
theorem default_locals_types (types : List valtype) (values : List val)
    (defaults : SourceMachine.defaultLocals (types.map local.LOCAL) = some values) :
    values.map Compiler.valueType = types := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, SourceMachine.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : SourceMachine.defaultValue ty with
    | none => simp [SourceMachine.defaultLocals, hv] at defaults
    | some value =>
      cases ht : SourceMachine.defaultLocals (types.map local.LOCAL) with
      | none => simp [SourceMachine.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [SourceMachine.defaultLocals, hv, ht] at defaults
        subst values
        simp only [List.map_cons, default_value_type hv, ih tail ht]

end Itasca.Runtime.Interp

end
