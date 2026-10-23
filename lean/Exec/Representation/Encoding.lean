import Exec.Representation.Layout
import SpecExt.Builtins.Float.Decoding

/-! Mathematical slot encoding used by the compiler/interpreter relation.
Slot words are naturals here; the concrete relation separately bounds them by
2^64. Reference addresses are store indices, with zero reserved for null. -/

namespace Exec.Code
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

theorem encodeValue_length (value : val) :
    (encodeValue value).length = width (valueType value) := by
  cases value with
  | CONST ty value => cases value <;> cases ty <;> rfl
  | VCONST ty value => cases ty; cases value; rfl
  | REF_NULL ty => cases ty <;> rfl
  | REF_FUNC_ADDR address => rfl
  | REF_HOST_ADDR address => rfl

theorem encodeValues_length (values : List val) :
    (encodeValues values).length = slots (values.map valueType) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [encodeValues, List.flatMap_cons, List.length_append, encodeValue_length,
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

theorem encodeValues_append (xs ys : List val) :
    encodeValues (xs ++ ys) = encodeValues xs ++ encodeValues ys := by
  exact List.flatMap_append

/-- The slot prefix ending at a value boundary encodes exactly that prefix of
values, even when it contains two-slot vectors. -/
theorem encodeValues_take (values : List val) (count : Nat) :
    (encodeValues values).take (offset (values.map valueType) count) =
      encodeValues (values.take count) := by
  have hs := encodeValues_append (values.take count) (values.drop count)
  rw [List.take_append_drop] at hs
  rw [hs]
  have hl : offset (values.map valueType) count = (encodeValues (values.take count)).length := by
    rw [encodeValues_length]
    simp only [offset, List.map_take]
  rw [hl, List.take_left]

end Exec.Code
