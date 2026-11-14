import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsRuntimeCommon
import Itasca.Support.Result
import SpecExt.Builtins.Float.Sign

/-!
Sections, each formerly its own module: StackLayout, Collection, Encoding, Values.
-/

/-! ## StackLayout -/

section

/-!
Validator stack widths and their slot-count interpretation. Compiler layout and source-demand proofs use this bridge without importing body construction.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def initializerWidth : Itasca.wasm_types.ValueType → U32
  | .V128 => 2#u32
  | _ => 1#u32

theorem compiler_width_eq (ty : Itasca.wasm_types.ValueType) :
    runtime.value.width ty = .ok (initializerWidth ty) := by
  cases ty <;> rfl

def compilerStackWidth : Itasca.code.StackType → Nat
  | .Val ty => width (Itasca.Translate.valueType ty)
  | .Bot => 1

def stackWords (values : List Itasca.code.StackType) : Nat :=
  (values.map compilerStackWidth).sum
end Itasca.Runtime.Compiler

end

/-! ## Collection -/

section

/-! Shared slice lookup and list transport lemmas for concrete representations. -/
namespace Itasca.Runtime.Representation
open Aeneas Aeneas.Std

theorem slice_index_given {T : Type} (values : Slice T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    Slice.index_usize values index ⦃ out => out = value ⦄ := by
  have bound : index.val < values.length := (List.getElem?_eq_some_iff.mp found).1
  step as ⟨out, hout⟩
  have read := List.getElem?_eq_getElem bound
  rw [found] at read
  exact hout.trans (Option.some.inj read).symm

theorem lookup_prefix {T : Type} (before after : List T)
    (retained : after.take before.length = before) {index : Nat} {value : T}
    (found : before[index]? = some value) : after[index]? = some value := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun values => values[index]?) retained
  have eq : after[index]? = before[index]? := by simpa [List.getElem?_take, bound] using same
  exact eq.trans found

theorem map_set_modify {T U : Type} (decode : T → U) (change : U → U)
    (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (same : decode replacement = change (decode old)) :
    (values.set index replacement).map decode = (values.map decode).modify index change := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst old
      simpa using same
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

end Itasca.Runtime.Representation

namespace Itasca.Runtime
open Aeneas Aeneas.Std

/-- The shared runtime `clear` helper empties any vector. -/
@[step] theorem runtime_clear {T : Type} (values : alloc.vec.Vec T) :
    runtime.clear values ⦃ out => out.val = [] ⦄ := by
  unfold runtime.clear runtime.clear_loop
  apply loop.spec_decr_nat (fun v => v.val.length) (fun _ => True)
  · intro v _
    simp only [runtime.clear_loop.body, alloc.vec.Vec.is_empty, bind_ok]
    split
    · rename_i empty
      simpa using empty
    · rename_i nonempty
      simp [alloc.vec.Vec.pop]
      have : 0 < v.val.length := List.length_pos_iff.mpr (by simpa using nonempty)
      omega
  · trivial

end Itasca.Runtime

end

/-! ## Encoding -/

section

/-! Mathematical slot encoding used by the compiler/interpreter relation.
Slot words are naturals here; the concrete relation separately bounds them by
2^64. Reference addresses are store indices, with zero reserved for null. -/

namespace Itasca.Runtime.Compiler
open SpecExt.Builtins

def valueType : val → valtype
  | .CONST ty _ => valtype_numtype ty
  | .VCONST _ _ => .V128
  | .REF_NULL .FUNCREF | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_NULL .EXTERNREF | .REF_HOST_ADDR _ => .EXTERNREF

def encodeValue : val → List Nat
  | .CONST _ (.mk_num__0 _ (.mk_uN bits)) => [bits]
  | .CONST ty (.mk_num__1 _ value) => [floatBits (sizenn ty) value]
  | .VCONST _ (.mk_uN bits) => [bits % 2 ^ 64, bits / 2 ^ 64]
  | .REF_NULL _ => [0]
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => [address + 1]

def encodeValues (values : List val) : List Nat := values.flatMap encodeValue

def decodeOne (ty : valtype) (words : List Nat) : Option (val × List Nat) :=
  match ty, words with
  | .I32, lo :: rest => some (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (lo % 2 ^ 32))), rest)
  | .I64, lo :: rest => some (.CONST .I64 (.mk_num__0 .I64 (.mk_uN lo)), rest)
  | .F32, lo :: rest => some (.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 lo)), rest)
  | .F64, lo :: rest => some (.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 lo)), rest)
  | .V128, lo :: hi :: rest => some (.VCONST .V128 (.mk_uN (lo + hi * 2 ^ 64)), rest)
  | .FUNCREF, lo :: rest =>
      some ((if lo = 0 then .REF_NULL .FUNCREF else .REF_FUNC_ADDR (lo - 1)), rest)
  | .EXTERNREF, lo :: rest =>
      some ((if lo = 0 then .REF_NULL .EXTERNREF else .REF_HOST_ADDR (lo - 1)), rest)
  | _, _ => none

theorem encode_value_length (value : val) :
    (encodeValue value).length = width (valueType value) := by
  cases value with
  | CONST ty value => cases value <;> cases ty <;> rfl
  | VCONST ty value => cases ty; cases value; rfl
  | REF_NULL ty => cases ty <;> rfl
  | REF_FUNC_ADDR address => rfl
  | REF_HOST_ADDR address => rfl

theorem encode_values_length (values : List val) :
    (encodeValues values).length = slots (values.map valueType) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [encodeValues, List.flatMap_cons, List.length_append, encode_value_length,
      List.map_cons, slots] at *
    rw [ih]

theorem decode_i32 {bits : Nat} (h : bits < 2 ^ 32) (rest : List Nat) :
    decodeOne .I32 (encodeValue (.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))) ++ rest) =
      some (.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits)), rest) := by
  simp only [encodeValue, List.cons_append, List.nil_append, decodeOne, Nat.mod_eq_of_lt h]

theorem decode_i64 (bits : Nat) (rest : List Nat) :
    decodeOne .I64 (encodeValue (.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits))) ++ rest) =
      some (.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits)), rest) := rfl

theorem decode_f32 (value : fN) (h : wf_fN 32 value) (rest : List Nat) :
    decodeOne .F32 (encodeValue (.CONST .F32 (.mk_num__1 .F32 value)) ++ rest) =
      some (.CONST .F32 (.mk_num__1 .F32 value), rest) := by
  change some (val.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (floatBits 32 value))), rest) = _
  rw [Float.float_roundtrip_32 value h]

theorem decode_f64 (value : fN) (h : wf_fN 64 value) (rest : List Nat) :
    decodeOne .F64 (encodeValue (.CONST .F64 (.mk_num__1 .F64 value)) ++ rest) =
      some (.CONST .F64 (.mk_num__1 .F64 value), rest) := by
  change some (val.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 (floatBits 64 value))), rest) = _
  rw [Float.float_roundtrip_64 value h]

theorem decode_vector (bits : Nat) (rest : List Nat) :
    decodeOne .V128 (encodeValue (.VCONST .V128 (.mk_uN bits)) ++ rest) =
      some (.VCONST .V128 (.mk_uN bits), rest) := by
  simp only [encodeValue, List.cons_append, List.nil_append, decodeOne]
  rw [Nat.mul_comm, Nat.mod_add_div]

theorem decode_function_ref (address : Nat) (rest : List Nat) :
    decodeOne .FUNCREF (encodeValue (.REF_FUNC_ADDR address) ++ rest) =
      some (.REF_FUNC_ADDR address, rest) := by
  simp [decodeOne, encodeValue]

theorem decode_external_ref (address : Nat) (rest : List Nat) :
    decodeOne .EXTERNREF (encodeValue (.REF_HOST_ADDR address) ++ rest) =
      some (.REF_HOST_ADDR address, rest) := by
  simp [decodeOne, encodeValue]

/-- Every well-formed specification value roundtrips through its typed slots.
Concrete machine-word and store-address bounds belong to the representation
invariant; this statement is about the mathematical encoding. -/
theorem decode_encode (value : val) (h : wf_val value) (rest : List Nat) :
    decodeOne (valueType value) (encodeValue value ++ rest) = some (value, rest) := by
  cases h with
  | val_case_0 ty value hv =>
    cases hv with
    | num__case_0 kind bits _ hb hty =>
      subst ty
      cases kind with
      | I32 =>
        cases hb with
        | uN_case_0 bits bounds =>
          change Nat at bits
          have hbound : bits ≤ 4294967295 := bounds.2
          exact decode_i32 (by omega) rest
      | I64 =>
        cases bits with
        | mk_uN bits => exact decode_i64 bits rest
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind with
      | F32 => exact decode_f32 value hv rest
      | F64 => exact decode_f64 value hv rest
  | val_case_1 ty value _ _ =>
    cases ty
    cases value with
    | mk_uN bits => exact decode_vector bits rest
  | val_case_2 ty => cases ty <;> rfl
  | val_case_3 address => exact decode_function_ref address rest
  | val_case_4 address => exact decode_external_ref address rest

theorem encode_values_append (xs ys : List val) :
    encodeValues (xs ++ ys) = encodeValues xs ++ encodeValues ys := by
  exact List.flatMap_append

/-- The slot prefix ending at a value boundary encodes exactly that prefix of
values, even when it contains two-slot vectors. -/
theorem encode_values_take (values : List val) (count : Nat) :
    (encodeValues values).take (offset (values.map valueType) count) =
      encodeValues (values.take count) := by
  have hs := encode_values_append (values.take count) (values.drop count)
  rw [List.take_append_drop] at hs
  rw [hs]
  have hl : offset (values.map valueType) count = (encodeValues (values.take count)).length := by
    rw [encode_values_length]
    simp only [offset, List.map_take]
  rw [hl, List.take_left]

end Itasca.Runtime.Compiler

end

/-! ## Values -/

section

/-!
Public runtime values, issued-reference ownership and source-value interpretation. Argument and result proofs use these conversions and slot-width facts.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def sourceType : Itasca.wasm_types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

@[step] theorem width_spec (ty : Itasca.wasm_types.ValueType) :
    runtime.value.width ty ⦃ result => result.val = Compiler.width (sourceType ty) ⦄ := by
  cases ty <;> simp [runtime.value.width, sourceType, Compiler.width]

def rawType : runtime.Value → Itasca.wasm_types.ValueType
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

def pairWords (ty : Itasca.wasm_types.ValueType) (pair : U64 × U64) : List Nat :=
  if sourceType ty = .V128 then [pair.1.val, pair.2.val] else [pair.1.val]

theorem source_value_type (value : runtime.Value) :
    Compiler.valueType (sourceValue value) = sourceType (rawType value) := by
  cases value with
  | FuncRef address => cases address <;> rfl
  | ExternRef address => cases address <;> rfl
  | _ => rfl

theorem source_value_wf (value : runtime.Value) : wf_val (sourceValue value) := by
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
      pairWords (rawType value) words = Compiler.encodeValue (sourceValue value) ⦄ := by
  cases value <;> simp only [runtime.value.encode, sourceValue, Compiler.encodeValue, rawType, pairWords, sourceType]
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

/-- The total slot width of a signature component, as computed by `value::type_slots`. -/
def valueTypeSlots (types : List Itasca.wasm_types.ValueType) : Nat :=
  Compiler.slots (types.map sourceType)

def ValueTypeSlotsState (types : List Itasca.wasm_types.ValueType) (total : Nat)
    (amount : Usize) (index : Usize) (overflow : Bool) : Prop :=
  if overflow then Usize.max < total
  else amount.val + valueTypeSlots (types.drop index.val) = total

@[step] theorem value_type_slots_loop (types : Slice Itasca.wasm_types.ValueType)
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
        simp only [valueTypeSlots, List.map_cons, Compiler.slots] at hs
        step as ⟨ty, hty⟩
        step with width_spec ty as ⟨word, hword⟩
        simp only [lift, bind_ok]
        have hw : (UScalar.cast .Usize word).val = Compiler.width (sourceType ty) := by
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
      cases overflow <;> simpa [ValueTypeSlotsState, same, valueTypeSlots, Compiler.slots] using hs
  · exact ⟨bound, state⟩

@[step] theorem value_type_slots (types : Slice Itasca.wasm_types.ValueType) :
    runtime.value.type_slots types ⦃ result =>
      match result with
      | some word => word.val = valueTypeSlots types.val
      | none => Usize.max < valueTypeSlots types.val ⦄ := by
  unfold runtime.value.type_slots
  step with value_type_slots_loop types 0#usize 0#usize false (valueTypeSlots types.val)
    (by simp) (by simp [ValueTypeSlotsState]) as ⟨amount, overflow, hs⟩
  cases overflow <;> simpa using hs

end Itasca.Runtime.Interp

end
