import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Lanes.EntryContractsAndShuffle
import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Compiler.Local.Lowering.Simd.ConstructionChecks
import Itasca.Runtime.Interp.Memory.MemoryEffects

/-!
Proofs for Runtime / Interp / Simd / Relations.

This module collects PureResultSlots, NumericResultSlots.
Each section documents its contracts and consumers.
-/

/-! ## PureResultSlots -/

section

open Itasca.Representation

/-! ## ShuffleRelation -/

section

/-!
Source-effect certificates for SIMD shuffle instructions.

Main declarations: `ShuffleSourceEffect` and `ShuffleEntrySound`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std Itasca.Body.Simd

theorem shuffle_byte_words (bits : BitVec 128) (low high : U64)
    (combined : bits.toNat = low.val+high.val*2^64) :
    Spec.Simd.byteWords bits = shuffleIndices low high := by
  apply List.ext_getElem?
  intro j
  have lowBound : low.val < 2^64 := by scalar_tac
  have highBound : high.val < 2^64 := by scalar_tac
  by_cases valid : j < 16
  · interval_cases j
    all_goals norm_num [Spec.Simd.byteWords,Spec.Simd.byteAt,shuffleIndices,unpackBytes,combined,Nat.div_div_eq_div_mul]
    all_goals omega
  · have left : (Spec.Simd.byteWords bits).length = 16 := Spec.Simd.byte_words_length _
    have right : (shuffleIndices low high).length = 16 := by simp [shuffleIndices,unpack_bytes_length]
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
end Itasca.Interp.Simd
namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std Itasca.Body.Simd

def ShuffleSourceEffect (low high : U64) (x y z value : BitVec 128) : Prop :=
  Step_pure ((Spec.Simd.operandValues [.V128,.V128] x y z).map admininstr_val ++
    [admininstr_instr (shuffle low high)])
    [admininstr_val (Spec.Simd.valueOfBits .V128 value)]

def ShuffleEntrySound {F : Type} (floats : runtime.platform.FloatOps F) : Prop :=
  ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) (low high : U64),
    bits.val = low.val+high.val*2^64 →
    (∀ lane ∈ shuffleIndices low high,proj_uN_0 lane < 32) →
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory
      ⦃ result => ∃ value,result = (.Ok value,memory) ∧ ShuffleSourceEffect low high x.bv y.bv z.bv value.bv ⦄

theorem shuffle_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) : ShuffleEntrySound floats := by
  intro offset laneIndex bits x y z memory low high combined bounded
  have indices := shuffle_byte_words bits.bv low high combined
  have allowed : ∀ j,j < 16 → Spec.Simd.byteAt bits.bv j < 32 := by
    intro j valid
    have member : uN.mk_uN (Spec.Simd.byteAt bits.bv j) ∈ Spec.Simd.byteWords bits.bv := by
      exact List.mem_map.mpr ⟨j,List.mem_range.mpr valid,rfl⟩
    rw [indices] at member
    exact bounded _ member
  apply WP.spec_mono (shuffle_dispatch_sound floats offset laneIndex bits x y z memory allowed)
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_⟩
  rw [indices] at source
  with_unfolding_all exact source
end Itasca.Interp.Simd

end

/-! ## PureResultSlots -/

section

/-!
Pure SIMD results represented in runtime slots.

Main declarations: `ValuesAt.simd_pure_result`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Body.Simd

theorem ValuesAt.simd_pure_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (signature : Signature) (value : U128)
    (before : List admininstr)
    (source : Step_pure before [admininstr_val (Simd.pureResult signature value.bv)])
    (capacity : base + Representation.slots (front.map Representation.valueType) +
      (Compiler.simdSourceWidth signature.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Representation.slots (front.map Representation.valueType))
      (Compiler.simdSourceWidth signature.outputs[0]?) value) base
      (front ++ [Simd.pureResult signature value.bv]) := by
  cases signature
  all_goals try exact represented.simd_vector_result value capacity
  have bound : value.val < 2^32 := Spec.pure_i32_bound source
  have cast : (UScalar.cast .U64 value).val = value.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have result := represented.simd_scalar_result .I32 value (by intro h; cases h)
    (by intro _; rw [cast]; exact bound) (by change base + Representation.slots _ + 1 ≤ words.length at capacity; omega)
  have decoded : Representation.decodeWords .I32 (UScalar.cast .U64 value) 0#u64 =
      Simd.pureResult .test value.bv := by
    change val.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((UScalar.cast .U64 value).val % 2^32))) = _
    rw [cast,Nat.mod_eq_of_lt bound]
    rfl
  rw [decoded] at result
  exact result
end Itasca.Interp

end

end

/-! ## NumericResultSlots -/

section

/-! ## Mutation -/

section

/-!
SIMD retains the store or replaces the opaque buffer of one issued memory without changing its length. Source semantics separately constrain its bytes.

Main declarations: `SimdStoreMutation`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- SIMD retains the store or replaces the opaque buffer of one issued memory
without changing its length. Source semantics separately constrain its bytes. -/
def SimdStoreMutation {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) : Prop :=
  after = before ∨ ∃ address object, before.memories.val[address.index.val]? = some object ∧
    MemoryMutation view before after address object

end Itasca.Interp

end

/-! ## NumericResultSlots -/

section

/-!
Numeric SIMD results represented in runtime slots.

Main declarations: `ValuesAt.simd_numeric_result`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem ValuesAt.simd_numeric_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : valtype) (value : U128)
    (numeric : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF ∧ ty ≠ .BOT)
    (small : ty = .I32 ∨ ty = .F32 → value.val < 2^32)
    (capacity : base + Representation.slots (front.map Representation.valueType) +
      (Compiler.simdSourceWidth (some ty)).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Representation.slots (front.map Representation.valueType))
      (Compiler.simdSourceWidth (some ty)) value) base
      (front ++ [Spec.Simd.valueOfBits ty value.bv]) := by
  have cast32 : (UScalar.cast .U64 value).val % 2^32 = value.val % 2^32 := by
    simp only [UScalar.cast_val_eq,UScalarTy.numBits]
    exact Nat.mod_mod_of_dvd _ (by norm_num)
  cases ty
  case V128 => exact represented.simd_vector_result value capacity
  case FUNCREF => exact False.elim (numeric.1 rfl)
  case EXTERNREF => exact False.elim (numeric.2.1 rfl)
  case BOT => exact False.elim (numeric.2.2 rfl)
  case I32 =>
    have bound := small (Or.inl rfl)
    have cast : (UScalar.cast .U64 value).val = value.val := by
      rw [UScalar.cast_val_eq];exact Nat.mod_eq_of_lt (by scalar_tac)
    have result := represented.simd_scalar_result .I32 value (by intro h; cases h)
      (by intro _;rw [cast];exact bound) (by change base + Representation.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Representation.decodeWords,Spec.Simd.valueOfBits,cast32,BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case I64 =>
    have result := represented.simd_scalar_result .I64 value (by intro h; cases h)
      (by intro h;rcases h with h|h <;>cases h) (by change base + Representation.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Representation.decodeWords,Spec.Simd.valueOfBits,UScalar.cast_val_eq,UScalarTy.numBits,
      BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case F32 =>
    have bound := small (Or.inr rfl)
    have cast : (UScalar.cast .U64 value).val = value.val := by
      rw [UScalar.cast_val_eq];exact Nat.mod_eq_of_lt (by scalar_tac)
    have result := represented.simd_scalar_result .F32 value (by intro h; cases h)
      (by intro _;rw [cast];exact bound) (by change base + Representation.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Representation.decodeWords,Spec.Simd.valueOfBits,cast32,BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case F64 =>
    have result := represented.simd_scalar_result .F64 value (by intro h; cases h)
      (by intro h;rcases h with h|h <;>cases h) (by change base + Representation.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Representation.decodeWords,Spec.Simd.valueOfBits,UScalar.cast_val_eq,UScalarTy.numBits,
      BitVec.toNat_setWidth,UScalar.bv_toNat] using result
end Itasca.Interp

end

end
