import Exec.Generated.Funs
import Exec.Representation.Encoding

namespace Exec.Interp
open Aeneas Aeneas.Std

def sourceType : Itasca.types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

@[step] theorem width_spec (ty : Itasca.types.ValueType) :
    runtime.value.width ty ⦃ result => result.val = Code.width (sourceType ty) ⦄ := by
  cases ty <;> simp [runtime.value.width, sourceType, Code.width]

def rawType : runtime.Value → Itasca.types.ValueType
  | .I32 _ => .I32
  | .I64 _ => .I64
  | .F32 _ => .F32
  | .F64 _ => .F64
  | .V128 _ => .V128
  | .FuncRef _ => .FuncRef
  | .ExternRef _ => .ExternRef

def ValueOwnedFits (store : Usize) : runtime.Value → Prop
  | .FuncRef (some a) => a.store = store ∧ a.index.val < Usize.max ∧ a.index.val < U64.max
  | .ExternRef (some a) => a.store = store ∧ a.index.val < Usize.max ∧ a.index.val < U64.max
  | _ => True

/-- Primitive API values roundtrip through their raw slot pair. Store identity
and address bounds are explicit for references. -/
theorem value_roundtrip (value : runtime.Value) (store : Usize)
    (hv : ValueOwnedFits store value) :
    (do let (lo, hi) ← runtime.value.encode value
        runtime.value.decode (rawType value) lo hi store) ⦃ result => result = value ⦄ := by
  cases value <;> simp only [runtime.value.encode, rawType, runtime.value.decode]
  all_goals simp [lift]
  case I32 v => scalar_tac
  case F32 v => scalar_tac
  case V128 v =>
    step
    step
    congr 1
    apply (UScalar.eq_equiv_bv_eq _ _).2
    simp only [UScalar.bv_or, UScalar.cast_bv_eq, i2_post1, x_post1]
    have bits (b : BitVec 128) :
        (BitVec.setWidth 128 (BitVec.setWidth 64 b)) |||
          ((BitVec.setWidth 128 (BitVec.setWidth 64 (b >>> 64))) <<< 64) = b := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      intro hi
      by_cases h : i < 64
      · simp [hi, h]
      · have hsub : i - 64 < 64 := by omega
        have hadd : 64 + (i - 64) = i := by omega
        simp [hi, h, hsub, hadd, show i - 64 < 128 by omega]
    exact bits v.bv
  case FuncRef a =>
    cases a with
    | none => simp
    | some a =>
      simp only [ValueOwnedFits] at hv
      rcases hv with ⟨hstore, hsize, h64⟩
      simp only
      step
      have hn : lo ≠ 0#u64 := by scalar_tac
      simp only [hn, ite_false]
      have hcast64 : (UScalar.cast .U64 a.index).val = a.index.val := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
        simpa [UScalarTy.numBits] using (show a.index.val < 2^64 by simpa [U64.max, U64.numBits] using Nat.lt_trans h64 (by simp [U64.max, U64.numBits]))
      have hloval : lo.val = a.index.val + 1 := by simpa [hcast64] using hi
      have hcastsize : (UScalar.cast .Usize lo).val = lo.val := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
        rw [hloval]
        simpa [UScalarTy.numBits, Usize.max, Usize.numBits] using (show a.index.val + 1 < 2^Usize.numBits by
          have hs : a.index.val < 2^Usize.numBits - 1 := by simpa only [Usize.max] using hsize
          omega)
      step as ⟨index, hindex⟩
      have he : index = a.index := by
        simp only [hcastsize, hloval] at hindex
        scalar_tac
      rw [he]
      cases a
      simp only at hstore
      cases hstore
      rfl
  case ExternRef a =>
    cases a with
    | none => simp
    | some a =>
      simp only [ValueOwnedFits] at hv
      rcases hv with ⟨hstore, hsize, h64⟩
      simp only
      step
      have hn : lo ≠ 0#u64 := by scalar_tac
      simp only [hn, ite_false]
      have hcast64 : (UScalar.cast .U64 a.index).val = a.index.val := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
        simpa [UScalarTy.numBits] using (show a.index.val < 2^64 by simpa [U64.max, U64.numBits] using Nat.lt_trans h64 (by simp [U64.max, U64.numBits]))
      have hloval : lo.val = a.index.val + 1 := by simpa [hcast64] using hi
      have hcastsize : (UScalar.cast .Usize lo).val = lo.val := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
        rw [hloval]
        simpa [UScalarTy.numBits, Usize.max, Usize.numBits] using (show a.index.val + 1 < 2^Usize.numBits by
          have hs : a.index.val < 2^Usize.numBits - 1 := by simpa only [Usize.max] using hsize
          omega)
      step as ⟨index, hindex⟩
      have he : index = a.index := by
        simp only [hcastsize, hloval] at hindex
        scalar_tac
      rw [he]
      cases a
      simp only at hstore
      cases hstore
      rfl

def sourceValue : runtime.Value → val
  | .I32 bits => .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))
  | .I64 bits => .CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))
  | .F32 bits => .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val))
  | .F64 bits => .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val))
  | .V128 bits => .VCONST .V128 (.mk_uN bits.val)
  | .FuncRef none => .REF_NULL .FUNCREF
  | .FuncRef (some address) => .REF_FUNC_ADDR address.index.val
  | .ExternRef none => .REF_NULL .EXTERNREF
  | .ExternRef (some address) => .REF_HOST_ADDR address.index.val

def pairWords (ty : Itasca.types.ValueType) (pair : U64 × U64) : List Nat :=
  if sourceType ty = .V128 then [pair.1.val, pair.2.val] else [pair.1.val]

theorem sourceValue_type (value : runtime.Value) :
    Code.valueType (sourceValue value) = sourceType (rawType value) := by
  cases value with
  | FuncRef address => cases address <;> rfl
  | ExternRef address => cases address <;> rfl
  | _ => rfl

theorem sourceValue_wf (value : runtime.Value) : wf_val (sourceValue value) := by
  cases value with
  | I32 bits =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I32 .I32 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ bits.val ∧ bits.val ≤ 4294967295
    scalar_tac
  | I64 bits =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I64 .I64 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ bits.val ∧ bits.val ≤ 18446744073709551615
    scalar_tac
  | F32 bits =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_32 bits.val (by scalar_tac)) rfl
  | F64 bits =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_64 bits.val (by scalar_tac)) rfl
  | V128 bits =>
    apply wf_val.val_case_1 _ _ (by decide)
    apply wf_uN.uN_case_0
    change 0 ≤ bits.val ∧ bits.val ≤ 340282366920938463463374607431768211455
    scalar_tac
  | FuncRef address =>
    cases address with
    | none => exact .val_case_2 _
    | some _ => exact .val_case_3 _
  | ExternRef address =>
    cases address with
    | none => exact .val_case_2 _
    | some _ => exact .val_case_4 _

/-- Actual word encoding agrees with the specification value encoding. -/
theorem encode_value_spec (value : runtime.Value) (store : Usize)
    (hv : ValueOwnedFits store value) :
    runtime.value.encode value ⦃ words =>
      pairWords (rawType value) words = Code.encodeValue (sourceValue value) ⦄ := by
  cases value <;> simp only [runtime.value.encode, sourceValue, Code.encodeValue, rawType, pairWords, sourceType]
  all_goals simp [lift]
  case F32 bits =>
    exact (SpecExt.Builtins.Float.float_bits_roundtrip_32 bits.val (by scalar_tac)).symm
  case F64 bits =>
    exact (SpecExt.Builtins.Float.float_bits_roundtrip_64 bits.val (by scalar_tac)).symm
  case V128 bits =>
    step as ⟨shifted, hshift, hbits⟩
    simp [UScalar.cast_val_eq, UScalarTy.numBits, hshift, Nat.shiftRight_eq_div_pow]
    scalar_tac
  case FuncRef a =>
    cases a with
    | none => simp
    | some a =>
      simp only [ValueOwnedFits] at hv
      step
      simp_all
  case ExternRef a =>
    cases a with
    | none => simp
    | some a =>
      simp only [ValueOwnedFits] at hv
      step
      simp_all

/-- Exact list update performed by the extracted slot writer. -/
def written (words : List U64) (position : Nat) (ty : Itasca.types.ValueType)
    (lo hi : U64) : List U64 :=
  if sourceType ty = .V128 then (words.set position lo).set (position + 1) hi
  else words.set position lo

@[step] theorem encode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (value : runtime.Value) (lo hi : U64)
    (he : runtime.value.encode value = .ok (lo, hi))
    (hb : position.val + Code.width (sourceType ty) ≤ slots.length) :
    runtime.interp.encode_slot slots position ty value ⦃ result =>
      result.val = written slots.val position.val ty lo hi ⦄ := by
  have hp : position.val < slots.length := by
    have := Code.width_positive (sourceType ty)
    omega
  unfold runtime.interp.encode_slot
  rw [he]
  step as ⟨old, back, hold, hback⟩
  subst back
  cases ty <;> simp only [runtime.value.width, sourceType, Code.width] at hb ⊢
  all_goals try simp [written, sourceType]
  step as ⟨next, hnext⟩
  step as ⟨after, hafter⟩
  subst after
  simp [hnext]

theorem index_eq (slots : Slice U64) (position : Usize) (word : U64)
    (hb : position.val < slots.length) (hv : slots.val[position.val]! = word) :
    Slice.index_usize slots position = .ok word := by
  obtain ⟨actual, hr, ha⟩ := WP.spec_imp_exists (Slice.index_usize_spec slots position hb)
  have he : actual = word := by simpa [ha, _root_.getElem!_pos slots.val position.val hb] using hv
  rw [he] at hr
  exact hr

/-- The extracted reader observes exactly the one or two words at its slot
boundary, then uses the extracted value decoder on those words. -/
@[step] theorem decode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (store : Usize) (lo hi : U64) (value : runtime.Value)
    (hb : position.val + Code.width (sourceType ty) ≤ slots.length)
    (hlo : slots.val[position.val]! = lo)
    (hhi : if sourceType ty = .V128 then slots.val[position.val + 1]! = hi else hi = 0#u64)
    (hd : runtime.value.decode ty lo hi store = .ok value) :
    runtime.interp.decode_slot slots position ty store ⦃ result => result = value ⦄ := by
  have hp : position.val < slots.length := by
    have := Code.width_positive (sourceType ty)
    omega
  have hread := index_eq slots position lo hp hlo
  cases ty <;> simp only [sourceType, reduceCtorEq, ↓reduceIte] at hhi
  all_goals first
    | solve | subst hi; simp [runtime.interp.decode_slot, runtime.value.width, hread, hd]
    | skip
  unfold runtime.interp.decode_slot
  simp [runtime.value.width]
  step as ⟨next, hnext⟩
  have hn : next.val < slots.length := by
    simp only [sourceType, Code.width] at hb
    omega
  have hnword : slots.val[next.val]! = hi := by simpa [hnext] using hhi
  have hreadHi := index_eq slots next hi hn hnword
  simp [hreadHi, hread, hd]

theorem written_length (words : List U64) (position : Nat) (ty : Itasca.types.ValueType)
    (lo hi : U64) : (written words position ty lo hi).length = words.length := by
  simp [written]; split <;> simp

theorem written_low (words : List U64) (position : Nat) (ty : Itasca.types.ValueType)
    (lo hi : U64) (hp : position < words.length) :
    (written words position ty lo hi)[position]! = lo := by
  unfold written
  split <;> simp [hp]

theorem written_high (words : List U64) (position : Nat) (ty : Itasca.types.ValueType)
    (lo hi : U64) (hv : sourceType ty = .V128) (hp : position + 1 < words.length) :
    (written words position ty lo hi)[position + 1]! = hi := by
  simp [written, hv, hp]

/-- Concrete slot write followed by concrete slot read preserves the API value
whenever its primitive encoding and decoding agree. -/
theorem slots_roundtrip (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (value : runtime.Value) (store : Usize) (lo hi : U64)
    (he : runtime.value.encode value = .ok (lo, hi))
    (hd : runtime.value.decode ty lo hi store = .ok value)
    (hz : sourceType ty ≠ .V128 → hi = 0#u64)
    (hb : position.val + Code.width (sourceType ty) ≤ slots.length) :
    (do let slots' ← runtime.interp.encode_slot slots position ty value
        runtime.interp.decode_slot slots' position ty store) ⦃ result => result = value ⦄ := by
  have hbval : position.val + Code.width (sourceType ty) ≤ slots.val.length := hb
  step with encode_slot_spec slots position ty value lo hi he hb as ⟨slots', hw⟩
  have hl : slots'.length = slots.length := by
    change slots'.val.length = slots.val.length
    rw [hw, written_length]
  apply decode_slot_spec slots' position ty store lo hi value (by simpa [hl] using hb)
  · rw [hw]
    exact written_low _ _ _ _ _ (by have := Code.width_positive (sourceType ty); omega)
  · by_cases hv : sourceType ty = .V128
    · simp only [hv, ↓reduceIte]
      rw [hw]
      exact written_high _ _ _ _ _ hv (by rw [hv] at hbval; simp only [Code.width] at hbval; omega)
    · simpa only [hv, ↓reduceIte] using hz hv
  · exact hd

theorem encode_hi_zero (value : runtime.Value) (store : Usize)
    (hv : ValueOwnedFits store value) :
    runtime.value.encode value ⦃ pair => sourceType (rawType value) ≠ .V128 → pair.2 = 0#u64 ⦄ := by
  cases value <;> simp [runtime.value.encode, rawType, sourceType, lift]
  case V128 bits => step
  case FuncRef address =>
    cases address with
    | none => simp
    | some a => simp only [ValueOwnedFits] at hv; step
  case ExternRef address =>
    cases address with
    | none => simp
    | some a => simp only [ValueOwnedFits] at hv; step

/-- Every representable, owned API value roundtrips through an in-bounds slot
region, using the actual extracted slot writer and reader. -/
theorem owned_slots_roundtrip (slots : Slice U64) (position : Usize)
    (value : runtime.Value) (store : Usize) (hv : ValueOwnedFits store value)
    (hb : position.val + Code.width (sourceType (rawType value)) ≤ slots.length) :
    (do let slots' ← runtime.interp.encode_slot slots position (rawType value) value
        runtime.interp.decode_slot slots' position (rawType value) store)
      ⦃ result => result = value ⦄ := by
  obtain ⟨⟨lo, hi⟩, he, hz⟩ := WP.spec_imp_exists (encode_hi_zero value store hv)
  have hr := value_roundtrip value store hv
  simp [he] at hr
  obtain ⟨result, hd, hv'⟩ := WP.spec_imp_exists hr
  subst result
  exact slots_roundtrip slots position (rawType value) value store lo hi he hd hz hb

/-- The total slot width of a signature component, as computed by `value::type_slots`. -/
def valueTypeSlots (types : List Itasca.types.ValueType) : Nat :=
  Code.slots (types.map sourceType)

def ValueTypeSlotsState (types : List Itasca.types.ValueType) (total : Nat)
    (amount : Usize) (index : Usize) (overflow : Bool) : Prop :=
  if overflow then Usize.max < total
  else amount.val + valueTypeSlots (types.drop index.val) = total

@[step] theorem value_type_slots_loop (types : Slice Itasca.types.ValueType)
    (amount : Usize) (index : Usize) (overflow : Bool) (total : Nat)
    (bound : index.val ≤ types.val.length)
    (state : ValueTypeSlotsState types.val total amount index overflow) :
    runtime.value.type_slots_loop types amount index overflow ⦃ out =>
      if out.2 then Usize.max < total else out.1.val = total ⦄ := by
  unfold runtime.value.type_slots_loop
  apply loop.spec_decr_nat (fun p => types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ types.val.length ∧ ValueTypeSlotsState types.val total p.1 p.2.1 p.2.2)
  · rintro ⟨amount, i, overflow⟩ ⟨hi, hs⟩
    dsimp only at hi hs
    unfold runtime.value.type_slots_loop.body
    dsimp only
    split
    · rename_i more
      have hb : i.val < types.val.length := by scalar_tac
      cases overflow with
      | true => simpa [ValueTypeSlotsState] using hs
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        simp only [ValueTypeSlotsState, Bool.false_eq_true, ite_false] at hs
        rw [List.drop_eq_getElem_cons hb] at hs
        simp only [valueTypeSlots, List.map_cons, Code.slots] at hs
        step as ⟨ty, hty⟩
        step with width_spec ty as ⟨word, hword⟩
        simp only [lift, bind_ok]
        have hw : (UScalar.cast .Usize word).val = Code.width (sourceType ty) := by
          simpa only [U32.cast_Usize_val_eq] using hword
        have hc := Usize.checked_add_bv_spec amount (UScalar.cast .Usize word)
        cases he : Usize.checked_add amount (UScalar.cast .Usize word) with
        | none =>
          simp only [he] at hc ⊢
          simp only [bind_ok, uncurry_apply_pair]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [ValueTypeSlotsState, ite_true]
          rw [← hty] at hs
          scalar_tac
        | some sum =>
          simp only [he] at hc ⊢
          simp only [bind_ok, uncurry_apply_pair]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [ValueTypeSlotsState, Bool.false_eq_true, ite_false, hnext, valueTypeSlots]
          rw [← hty] at hs
          scalar_tac
    · rename_i finished
      have same : i.val = types.val.length := by scalar_tac
      cases overflow <;> simpa [ValueTypeSlotsState, same, valueTypeSlots, Code.slots] using hs
  · exact ⟨bound, state⟩

@[step] theorem value_type_slots (types : Slice Itasca.types.ValueType) :
    runtime.value.type_slots types ⦃ result =>
      match result with
      | some word => word.val = valueTypeSlots types.val
      | none => Usize.max < valueTypeSlots types.val ⦄ := by
  unfold runtime.value.type_slots
  step with value_type_slots_loop types 0#usize 0#usize false (valueTypeSlots types.val)
    (by simp) (by simp [ValueTypeSlotsState]) as ⟨amount, overflow, hs⟩
  cases overflow <;> simpa using hs

end Exec.Interp
