import Itasca.Runtime.Interp.Relations.Range
import SpecExt.Builtins.Examples
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Interp.State.TableAccess

/-!
Sections, each formerly its own module: MemoryAddress, MemoryScalar, MemoryEncoding, MemoryDecode, MemoryDispatch, MemoryCoreTransition, MemorySize.
-/

/-! ## MemoryAddress -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Scalar accesses use a mathematical 33-bit effective address. Both supported
machine-index widths agree on the exact endpoint test; failed checks trap. -/
def MemoryAddressEffect (address offset : U32) (width bytes : Usize)
    (result : core.result.Result Usize runtime.ExecError) : Prop :=
  if address.val + offset.val + width.val ≤ bytes.val then
    ∃ start, result = .Ok start ∧ start.val = address.val + offset.val
  else result = .Err (.Trap .MemoryOutOfBounds)

@[step] theorem memory_address_effect (address offset : U32) (width bytes : Usize) :
    runtime.interp.memory.address address offset width bytes
      ⦃ result => MemoryAddressEffect address offset width bytes result ⦄ := by
  have widthCast := usize_to_u64_exact width
  unfold runtime.interp.memory.address
  simp only [lift, bind_ok]
  step as ⟨start, hstart⟩
  step with range_effect start (UScalar.cast .U64 width) bytes .MemoryOutOfBounds as ⟨r, hr⟩
  simp only [RangeEffect] at hr
  split at hr
  · rename_i fits
    obtain ⟨range, rfl, hstartEq, _⟩ := hr
    have inside : address.val + offset.val + width.val ≤ bytes.val := by scalar_tac
    simp [core.result.Result.Insts.CoreOpsTry.branch, MemoryAddressEffect, inside]
    scalar_tac
  · rename_i outside
    subst hr
    have notInside : ¬ address.val + offset.val + width.val ≤ bytes.val := by scalar_tac
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, MemoryAddressEffect, notInside]
end Itasca.Runtime.Interp

end

/-! ## MemoryScalar -/

section

/-!
Scalar memory byte encoding and handler effects. Exact little-endian byte calculations establish load/store widths, loaded words and the extracted scalar operation effects.
-/

/-! ## Memory Bytes -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarStoreByte (value : U64) (index : Nat) : U8 :=
  ⟨BitVec.ofNat 8 (value.val >>> (index * 8))⟩

def scalarStoreBytes (bytes : List U8) (start : Nat) (value : U64) (index : Nat) : Nat → List U8
  | 0 => bytes
  | count + 1 => scalarStoreBytes (bytes.set (start + index) (scalarStoreByte value index)) start value (index + 1) count

theorem scalar_store_bytes_length (bytes : List U8) (start : Nat) (value : U64) (index count : Nat) :
    (scalarStoreBytes bytes start value index count).length = bytes.length := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih => simp only [scalarStoreBytes, ih, List.length_set]

/-- The complete extracted store loop terminates and writes precisely the
selected little-endian bytes, without changing the buffer length. -/
@[step] theorem memory_store_loop_effect (value : U64) (bytes : Slice U8) (width start index : Usize)
    (small : width.val ≤ 8) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.memory.store_loop value bytes width start index ⦃ out =>
      out.val = scalarStoreBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.memory.store_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧ p.1.length = bytes.length ∧
      scalarStoreBytes p.1.val start.val value p.2.val (width.val - p.2.val) =
        scalarStoreBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, lengthEq, effect⟩
    dsimp only at bound lengthEq effect
    unfold runtime.interp.memory.store_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨destination, destinationEq⟩
      step as ⟨byte, byteCast⟩
      step as ⟨updated, updatedEq⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simpa [updatedEq] using lengthEq
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, scalarStoreBytes] at effect
        have byteEq : UScalar.cast .U8 shifted = scalarStoreByte value position.val := by
          apply UScalar.eq_of_val_eq
          change (UScalar.cast .U8 shifted).val = (value.val >>> (position.val * 8)) % 256
          rw [UScalar.cast_val_eq, shiftedEq, shiftEq]
          rfl
        simpa only [updatedEq, Slice.set_val_eq, destinationEq, nextEq, byteCast, byteEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, scalarStoreBytes] using effect
  · exact ⟨initial, rfl, rfl⟩
/-- Little-endian accumulation in the machine word, with explicit byte position. -/
def scalarLoadByte (value : U64) (byte : U8) (index : Nat) : U64 :=
  value ||| (⟨(UScalar.cast .U64 byte).bv <<< (index * 8)⟩ : U64)

def scalarLoadBytes (bytes : List U8) (start : Nat) (value : U64) (index : Nat) : Nat → U64
  | 0 => value
  | count + 1 => scalarLoadBytes bytes start
      (scalarLoadByte value bytes[start + index]! index) (index + 1) count

/-- The extracted load loop terminates and accumulates exactly the requested
bytes, preserving their little-endian order. -/
@[step] theorem memory_load_loop_effect (bytes : Slice U8) (width start : Usize) (value : U64) (index : Usize)
    (small : width.val ≤ 8) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.memory.load_loop bytes width start value index ⦃ out =>
      out = scalarLoadBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.memory.load_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧
      scalarLoadBytes bytes.val start.val p.1 p.2.val (width.val - p.2.val) =
        scalarLoadBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, effect⟩
    dsimp only at bound effect
    unfold runtime.interp.memory.load_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨source, sourceEq⟩
      step as ⟨byte, byteEq⟩
      step with Aeneas.Step.specLiftDef (UScalar.cast .U64 byte) as ⟨wide, wideEq⟩
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨updated, updatedEq, updatedBits⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, scalarLoadBytes] at effect
        have read : byte = bytes.val[start.val + position.val]! := by
          have bound : start.val + position.val < bytes.val.length := by change start.val + position.val < bytes.length; omega
          rw [getElem!_pos bytes.val _ bound]
          simpa only [sourceEq] using byteEq
        have update : updated = scalarLoadByte current bytes.val[start.val + position.val]! position.val := by
          apply U64.bv_eq_imp_eq
          rw [updatedBits, shiftedBits, wideEq, read, shiftEq]
          rfl
        simpa only [update, nextEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, scalarLoadBytes] using effect
  · exact ⟨initial, rfl⟩
end Itasca.Runtime.Interp

end

/-! ## Memory Scalar -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarLoadWidth (opcode : U16) : Usize :=
  match opcode with
  | 40#uscalar | 42#uscalar | 52#uscalar | 53#uscalar => 4#usize
  | 41#uscalar | 43#uscalar => 8#usize
  | 46#uscalar | 47#uscalar | 50#uscalar | 51#uscalar => 2#usize
  | _ => 1#usize

def scalarStoreWidth (opcode : U16) : Usize :=
  match opcode with
  | 54#uscalar | 56#uscalar | 62#uscalar => 4#usize
  | 55#uscalar | 57#uscalar => 8#usize
  | 59#uscalar | 61#uscalar => 2#usize
  | _ => 1#usize

def scalarLoadedWord (opcode : U16) (word : U64) : U64 :=
  match opcode with
  | 44#uscalar => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))
  | 46#uscalar => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))
  | 48#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I8 word))
  | 50#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I16 word))
  | 52#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 word))
  | _ => word

theorem scalar_load_width_bound (opcode : U16) : (scalarLoadWidth opcode).val ≤ 8 := by
  unfold scalarLoadWidth
  split <;> decide

theorem scalar_store_width_bound (opcode : U16) : (scalarStoreWidth opcode).val ≤ 8 := by
  unfold scalarStoreWidth
  split <;> decide

private theorem load_unfold (opcode : U16) (address offset : U32) (bytes : Slice U8) :
    runtime.interp.memory.load opcode address offset bytes = (do
      let result ← runtime.interp.memory.address address offset (scalarLoadWidth opcode) (Slice.len bytes)
      match result with
      | .Err error => .ok (.Err error)
      | .Ok start =>
        let word ← runtime.interp.memory.load_loop bytes (scalarLoadWidth opcode) start 0#u64 0#usize
        .ok (.Ok (scalarLoadedWord opcode word))) := by
  unfold runtime.interp.memory.load scalarLoadWidth
  split <;> simp only [bind_ok]
  all_goals
    congr 1
    funext result
    cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]
  all_goals
    congr 1 <;> (funext word; simp [scalarLoadedWord, lift, bind_ok])
  all_goals split <;> simp_all [scalarLoadedWord, lift, bind_ok]

private theorem store_unfold (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8) :
    runtime.interp.memory.store opcode address offset value bytes = (do
      let result ← runtime.interp.memory.address address offset (scalarStoreWidth opcode) (Slice.len bytes)
      match result with
      | .Err error => .ok (.Err error,bytes)
      | .Ok start =>
        let after ← runtime.interp.memory.store_loop value bytes (scalarStoreWidth opcode) start 0#usize
        .ok (.Ok (),after)) := by
  unfold runtime.interp.memory.store scalarStoreWidth
  split <;> simp only [bind_ok]
  all_goals
    congr 1
    funext result
    cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]

def ScalarLoadEffect (opcode : U16) (address offset : U32) (bytes : Slice U8)
    (result : core.result.Result U64 runtime.ExecError) : Prop :=
  if address.val + offset.val + (scalarLoadWidth opcode).val ≤ bytes.length then
    result = .Ok (scalarLoadedWord opcode (scalarLoadBytes bytes.val (address.val + offset.val)
      0#u64 0 (scalarLoadWidth opcode).val))
  else result = .Err (.Trap .MemoryOutOfBounds)

def ScalarStoreEffect (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8)
    (out : core.result.Result Unit runtime.ExecError × Slice U8) : Prop :=
  if address.val + offset.val + (scalarStoreWidth opcode).val ≤ bytes.length then
    out.1 = .Ok () ∧ out.2.val = scalarStoreBytes bytes.val (address.val + offset.val)
      value 0 (scalarStoreWidth opcode).val
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

/-- Every scalar load either returns its exact little-endian value or the
specified bounds trap; the extracted computation itself never fails. -/
@[step] theorem memory_load_effect (opcode : U16) (address offset : U32) (bytes : Slice U8) :
    runtime.interp.memory.load opcode address offset bytes ⦃ ScalarLoadEffect opcode address offset bytes ⦄ := by
  rw [load_unfold]
  step with memory_address_effect address offset (scalarLoadWidth opcode) (Slice.len bytes) as ⟨result, effect⟩
  by_cases fits : address.val + offset.val + (scalarLoadWidth opcode).val ≤ bytes.length
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    step with memory_load_loop_effect bytes (scalarLoadWidth opcode) start 0#u64 0#usize
      (scalar_load_width_bound opcode) (by omega) (by simp) as ⟨word,wordEq⟩
    simpa [ScalarLoadEffect,fits,wordEq,startEq]
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_false] at effect
    rw [effect]
    simp [ScalarLoadEffect,fits]

/-- Scalar stores preserve the exact original buffer on a bounds trap. -/
@[step] theorem memory_store_effect (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8) :
    runtime.interp.memory.store opcode address offset value bytes ⦃ ScalarStoreEffect opcode address offset value bytes ⦄ := by
  rw [store_unfold]
  step with memory_address_effect address offset (scalarStoreWidth opcode) (Slice.len bytes) as ⟨result, effect⟩
  by_cases fits : address.val + offset.val + (scalarStoreWidth opcode).val ≤ bytes.length
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    step with memory_store_loop_effect value bytes (scalarStoreWidth opcode) start 0#usize
      (scalar_store_width_bound opcode) (by omega) (by simp) as ⟨after,afterEq⟩
    simpa [ScalarStoreEffect,fits,afterEq,startEq]
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_false] at effect
    rw [effect]
    simp [ScalarStoreEffect,fits]
end Itasca.Runtime.Interp

end

end

/-! ## MemoryEncoding -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

private theorem power_byte (index : Nat) : 2^(index * 8) = 256^index := by
  rw [Nat.mul_comm, Nat.pow_mul]

theorem scalar_load_byte_value (value : U64) (byte : U8) (index : Nat)
    (small : index < 8) (lowerBound : value.val < 256^index) :
    (scalarLoadByte value byte index).val = value.val + byte.val * 256^index := by
  have byteBound : byte.val < 256 := by scalar_tac
  have shiftedBound : byte.val * 256^index < 2^64 := by
    interval_cases index <;> norm_num at * <;> omega
  change (value.bv ||| ((UScalar.cast .U64 byte).bv <<< (index * 8))).toNat = _
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, UScalar.bv_toNat, U8.cast_U64_val_eq]
  rw [Nat.shiftLeft_eq, power_byte, Nat.mod_eq_of_lt shiftedBound]
  have separated := Nat.two_pow_add_eq_or_of_lt (i := index * 8) (by simpa only [power_byte] using lowerBound) byte.val
  simpa only [power_byte, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using separated.symm
/-- The byte loop is the specification's little-endian natural-number decoder,
with an explicit already-filled low prefix. -/
theorem scalar_load_bytes_value (bytes : List U8) (start : Nat) (value : U64) (index count : Nat)
    (small : index + count ≤ 8) (inside : start + index + count ≤ bytes.length)
    (lowerBound : value.val < 256^index) :
    (scalarLoadBytes bytes start value index count).val = value.val + 256^index *
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop (start + index)).take count)) := by
  induction count generalizing value index with
  | zero => simp [scalarLoadBytes, Store.decodeBytes, SpecExt.Builtins.integerOfBytes]
  | succ count ih =>
    have atIndex : start + index < bytes.length := by omega
    have byteBound : bytes[start + index]!.val < 256 := by scalar_tac
    have nextValue := scalar_load_byte_value value bytes[start + index]! index (by omega) lowerBound
    have nextBound : (scalarLoadByte value bytes[start + index]! index).val < 256^(index+1) := by
      rw [nextValue,Nat.pow_succ]
      have positive : 0 < 256^index := by positivity
      nlinarith
    rw [scalarLoadBytes, ih _ (index+1) (by omega) (by omega) nextBound, nextValue]
    rw [List.drop_eq_getElem_cons atIndex]
    simp only [List.take_succ_cons, Store.decodeBytes, List.map_cons, SpecExt.Builtins.integerOfBytes]
    rw [getElem!_pos bytes _ atIndex, Nat.pow_succ]
    have positions : start + (index+1) = start + index + 1 := by omega
    rw [positions]
    ring

theorem scalar_load_bytes_source (bytes : List U8) (start count : Nat)
    (small : count ≤ 8) (inside : start + count ≤ bytes.length) :
    (scalarLoadBytes bytes start 0#u64 0 count).val =
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop start).take count)) := by
  simpa using scalar_load_bytes_value bytes start 0#u64 0 count (by simpa using small)
    (by simpa using inside) (by simp)
end Itasca.Runtime.Interp

end

/-! ## MemoryDecode -/

section

/-!
Scalar memory source decoding. Load-word decoding and store-payload byte correspondence establish how concrete lookup, unchanged memory and writes appear in the decoded source store.
-/

/-! ## Memory Load Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

def numericLoadOpcode : numtype → U16
  | .I32 => 40#u16
  | .I64 => 41#u16
  | .F32 => 42#u16
  | .F64 => 43#u16

def numericMemoryType : numtype → Itasca.wasm_types.ValueType
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64

private theorem machine_bytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem numeric_load_word_decodes (ty : numtype) (bytes : List U8) (start : Nat)
    (inside : start + Spec.scalarNumBytes ty ≤ bytes.length) :
    Store.decodeWords (numericMemoryType ty)
      (scalarLoadBytes bytes start 0#u64 0 (Spec.scalarNumBytes ty)) 0#u64 =
      .CONST ty (inv_nbytes_ ty (Store.decodeBytes ((bytes.drop start).take (Spec.scalarNumBytes ty)))) := by
  have width : Spec.scalarNumBytes ty ≤ 8 := by cases ty <;> decide
  have wordEq := scalar_load_bytes_source bytes start (Spec.scalarNumBytes ty) width inside
  have payloadWf := machine_bytes_wf ((bytes.drop start).take (Spec.scalarNumBytes ty))
  have payloadLength : (Store.decodeBytes ((bytes.drop start).take (Spec.scalarNumBytes ty))).length = Spec.scalarNumBytes ty := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  have bounded := Spec.integer_of_bytes_bound _ payloadWf
  rw [payloadLength] at bounded
  cases ty <;> simp only [numericMemoryType,Store.decodeWords,wordEq,inv_nbytes_,inv_ibytes_,inv_fbytes_]
  · rw [Nat.mod_eq_of_lt (by simpa [Spec.scalarNumBytes] using bounded)]
  · rw [Nat.mod_eq_of_lt (by simpa [Spec.scalarNumBytes] using bounded)]

end Itasca.Runtime.Interp

end

/-! ## Memory Store Encoding -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarStorePayload (value : U64) (width : Nat) : List U8 :=
  (List.range width).map (scalarStoreByte value)

private theorem scalar_store_payload_at (value : U64) (width index : Nat) (inside : index < width) :
    (scalarStorePayload value width)[index]! = scalarStoreByte value index := by
  simp [scalarStorePayload,List.getElem!_eq_getElem?_getD,inside]

theorem scalar_store_bytes_copy_into (bytes : List U8) (start : Nat) (value : U64) (width index count : Nat)
    (inside : index + count ≤ width) :
    scalarStoreBytes bytes start value index count =
      Spec.Segment.copyInto bytes (scalarStorePayload value width) (start+index) index count := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih =>
    simp only [scalarStoreBytes,Spec.Segment.copyInto]
    rw [scalar_store_payload_at value width index (by omega)]
    simpa only [Nat.add_assoc] using ih (bytes.set (start+index) (scalarStoreByte value index)) (index+1) (by omega)

theorem scalar_store_bytes_set_slice (bytes : List U8) (start : Nat) (value : U64) (width : Nat)
    (inside : start + width ≤ bytes.length) :
    scalarStoreBytes bytes start value 0 width = bytes.setSlice! start (scalarStorePayload value width) := by
  rw [scalar_store_bytes_copy_into bytes start value width 0 width (by omega)]
  simp only [Nat.add_zero]
  rw [Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ (by simp [scalarStorePayload]) inside]
  simp only [List.slice_zero_j, Nat.zero_add]
  rw [List.take_of_length_le (by simp [scalarStorePayload])]

private theorem integer_bytes_at (count value index : Nat) (inside : index < count) :
    (SpecExt.Builtins.integerBytes count value)[index]? = some (.mk_byte ((value / 256^index) % 256)) := by
  induction index generalizing count value with
  | zero => cases count <;> simp_all [SpecExt.Builtins.integerBytes]
  | succ index ih =>
    cases count with
    | zero => omega
    | succ count =>
      simpa only [SpecExt.Builtins.integerBytes,List.getElem?_cons_succ,Nat.pow_succ,
        Nat.div_div_eq_div_mul,Nat.mul_comm] using ih count (value/256) (by omega)

theorem scalar_store_payload_source (value : U64) (width : Nat) :
    Store.decodeBytes (scalarStorePayload value width) = SpecExt.Builtins.integerBytes width value.val := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < width
  · rw [integer_bytes_at width value.val index inside]
    simp only [Store.decodeBytes,scalarStorePayload,List.getElem?_map]
    simp only [List.getElem?_range inside,Option.map_some]
    congr 2
    change (value.val >>> (index*8)) % 256 = (value.val / 256^index) % 256
    rw [Nat.shiftRight_eq_div_pow]
    congr 2
    rw [Nat.mul_comm, Nat.pow_mul]
  · have outside : width ≤ index := by omega
    rw [List.getElem?_eq_none (by simpa [Store.decodeBytes,scalarStorePayload] using outside),
      List.getElem?_eq_none (by simpa only [SpecExt.Builtins.integerBytes_length] using outside)]

theorem scalar_store_bytes_source (bytes : List U8) (start : Nat) (value : U64) (width : Nat)
    (inside : start+width ≤ bytes.length) :
    Store.decodeBytes (scalarStoreBytes bytes start value 0 width) =
      (Store.decodeBytes bytes).setSlice! start (SpecExt.Builtins.integerBytes width value.val) := by
  rw [scalar_store_bytes_set_slice bytes start value width inside]
  unfold Store.decodeBytes
  rw [List.map_setSlice!]
  rw [show (scalarStorePayload value width).map (fun b => byte.mk_byte b.val) =
    SpecExt.Builtins.integerBytes width value.val from scalar_store_payload_source value width]
end Itasca.Runtime.Interp

end

/-! ## Memory Store Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

def numericStoreOpcode : numtype → U16
  | .I32 => 54#u16
  | .I64 => 55#u16
  | .F32 => 56#u16
  | .F64 => 57#u16

def numericStoreValue (ty : numtype) (word : U64) : num_ :=
  match ty with
  | .I32 => .mk_num__0 .I32 (.mk_uN (word.val % 2^32))
  | .I64 => .mk_num__0 .I64 (.mk_uN word.val)
  | .F32 => .mk_num__1 .F32 (Builtins.floatOfBits 32 (word.val % 2^32))
  | .F64 => .mk_num__1 .F64 (Builtins.floatOfBits 64 word.val)

theorem numeric_store_value_decodes (ty : numtype) (word : U64) :
    Store.decodeWords (numericMemoryType ty) word 0#u64 = .CONST ty (numericStoreValue ty word) := by
  cases ty <;> rfl

theorem numeric_store_value_bytes (ty : numtype) (word : U64) :
    nbytes_ ty (numericStoreValue ty word) = Builtins.integerBytes (Spec.scalarNumBytes ty) word.val := by
  cases ty
  · simpa [nbytes_,numericStoreValue,ibytes_,proj_uN_0,Spec.scalarNumBytes] using Spec.integer_bytes_mod 4 word.val
  · rfl
  · have bits := Builtins.Float.float_bits_roundtrip_32 (word.val % 2^32) (Nat.mod_lt _ (by norm_num))
    change Builtins.integerBytes 4 (Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))) = _
    rw [bits]
    exact Spec.integer_bytes_mod 4 word.val
  · have bits := Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)
    simp [nbytes_,numericStoreValue,fbytes_,bits,Spec.scalarNumBytes]

end Itasca.Runtime.Interp

end

/-! ## Memory Decode -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

theorem memory_lookup_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object) :
    fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view object := by
  simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]

/-- Replacing an opaque buffer with an equal byte view preserves the complete
source store, regardless of the callback's representation of that buffer. -/
theorem memory_unchanged_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (buffer : M) (found : store.memories.val[address.index.val]? = some object)
    (unchanged : view buffer = view object.buf) :
    decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} =
      decodeStore view code store := by
  rw [decode_store_memory_update]
  have same : decodeMemory view {object with buf := buffer} = decodeMemory view object := by
    simp only [decodeMemory,unchanged]
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view) id store.memories.val address.index.val
    object {object with buf := buffer} found same
  simp only [alloc.vec.Vec.set_val_eq,lists,List.modify_id]
  rfl

/-- A byte-exact write decodes to the generated memory update. The unchanged
length retains the source memory type and every unrelated object. -/
theorem memory_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (buffer : M)
    (start : Nat) (payload : List byte)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object)
    (inside : start + payload.length ≤ (view object.buf).length)
    (written : decodeBytes (view buffer).val = (decodeBytes (view object.buf).val).setSlice! start payload) :
    decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} =
      Spec.memoryPayloadWrite (decodeStore view code store) ambient start payload := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have lengthEq : (view buffer).length = (view object.buf).length := by
    simpa only [decodeBytes,List.length_map,List.length_setSlice!,Slice.length] using congrArg List.length written
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := splice m.BYTES payload start})
    store.memories.val address.index.val object {object with buf := buffer} found
    (by simp only [decodeMemory,lengthEq,Spec.splice_set_slice (decodeBytes (view object.buf).val) payload start (by simpa [decodeBytes] using inside),written])
  unfold Spec.memoryPayloadWrite
  rw [memoryRead,decode_store_memory_update]
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl
end Itasca.Runtime.Interp

end

end

/-! ## MemoryDispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Loads trap before modifying execution slots, and successful loads write only
the designated result slot. Memory access is through the explicit dictionary law. -/
theorem execute_load_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (opcode : U16) (dst address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M) (addressWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (capacity : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_load memory exec store instanceIndex base opcode dst address offset ⦃ out =>
      if (UScalar.cast .U32 addressWord).val + offset.val + (scalarLoadWidth opcode).val ≤ (view object.buf).length then
        out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val + dst.val)
          (scalarLoadedWord opcode (scalarLoadBytes (view object.buf).val
            ((UScalar.cast .U32 addressWord).val + offset.val) 0#u64 0 (scalarLoadWidth opcode).val)))
      else out = (.Err (.Trap .MemoryOutOfBounds),exec) ⦄ := by
  have inputBound : base.val + address.val < exec.slots.length := (List.getElem?_eq_some_iff.mp input).1
  unfold runtime.interp.execute_load
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize memoryAddress (by simpa using mapped) as ⟨actual,actualEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  step with vec_index_given exec.slots position addressWord (by simpa only [positionEq,U32.cast_Usize_val_eq] using input) as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given store.memories memoryAddress.index object issued as ⟨actual,actualEq⟩
  subst actual
  rw [laws.read,bind_ok]
  step with memory_load_effect opcode (UScalar.cast .U32 addressWord) offset (view object.buf) as ⟨result,effect⟩
  unfold ScalarLoadEffect at effect
  split at effect
  · rename_i fits
    rw [effect]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,lift,if_pos fits]
    step as ⟨destination,destinationEq⟩
    step as ⟨old,back,oldEq,backEq⟩
    simp [SlotsEffect,backEq,destinationEq]
  · rename_i outside
    rw [effect]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,outside]
    scalar_tac

/-- The complete store dispatch retains every object except the selected memory
buffer. Even on a bounds trap, the callback's opaque representation may change;
its decoded bytes remain exactly unchanged. -/
theorem execute_store_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (opcode : U16) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M) (addressWord valueWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val + address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val + value.val]? = some valueWord) :
    runtime.interp.execute_store memory exec store instanceIndex base opcode address value offset ⦃ out =>
      ∃ buffer, out.2 = {store with memories := store.memories.set memoryAddress.index {object with buf := buffer}} ∧
        ScalarStoreEffect opcode (UScalar.cast .U32 addressWord) offset valueWord (view object.buf) (out.1,view buffer) ⦄ := by
  have inputBound : base.val + address.val < exec.slots.length := (List.getElem?_eq_some_iff.mp input).1
  have valueBound : base.val + value.val < exec.slots.length := (List.getElem?_eq_some_iff.mp inputValue).1
  unfold runtime.interp.execute_store
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize memoryAddress (by simpa using mapped) as ⟨actual,actualEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  step with vec_index_given exec.slots position addressWord (by simpa only [positionEq,U32.cast_Usize_val_eq] using input) as ⟨actual,actualEq⟩
  subst actual
  step as ⟨valuePosition,valuePositionEq⟩
  step with vec_index_given exec.slots valuePosition valueWord (by simpa only [valuePositionEq,U32.cast_Usize_val_eq] using inputValue) as ⟨actual,actualEq⟩
  subst actual
  have objectBound : memoryAddress.index.val < store.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  step as ⟨old,back,oldEq,backEq⟩
  have oldSame : old = object := by
    have atIndex := List.getElem?_eq_getElem objectBound
    rw [issued] at atIndex
    exact oldEq.trans (Option.some.inj atIndex).symm
  subst old
  rw [oldSame]
  obtain ⟨writeBack,writeEq,writeLaw⟩ := laws.write object.buf
  rw [writeEq,bind_ok]
  step with memory_store_effect opcode (UScalar.cast .U32 addressWord) offset valueWord (view object.buf) as ⟨status,written,effect⟩
  have lengthEq : written.length = (view object.buf).length := by
    unfold ScalarStoreEffect at effect
    split at effect
    · obtain ⟨_,bytesEq⟩ := effect
      change written.val.length = (view object.buf).val.length
      rw [bytesEq,scalar_store_bytes_length]
    · have same := congrArg Prod.snd effect
      simpa using congrArg Slice.length same
  have restored := writeLaw written lengthEq
  refine ⟨writeBack written,?_,?_⟩
  · simp [backEq]
  · simpa only [restored] using effect
end Itasca.Runtime.Interp

end

/-! ## MemoryCoreTransition -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor

theorem core_step_load_eq (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Load) (argument : memarg) :
    SourceMachine.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      SourceMachine.Core.load ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Memory.Load.source,SourceMachine.Memory.decode_load_descriptor]
  rfl

theorem core_step_store_eq (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Store) (argument : memarg) :
    SourceMachine.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      SourceMachine.Core.store ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Memory.Store.source,SourceMachine.Memory.decode_store_descriptor]
  rfl
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## MemorySize -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact MEMORY_SIZE read and result-slot write; memory bytes are observed
through the platform law and the store remains unchanged. -/
theorem memory_size_handler {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (issued : store.memories.val[address.index.val]? = some object)
    (slotBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_memory_size memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ pages : Usize, pages.val = (view object.buf).length / 65536 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 pages)) ⦄ := by
  unfold runtime.interp.execute_memory_size
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize address mapped as ⟨actual,addressEq⟩
  subst actual
  step with vec_index_given store.memories address.index object issued as ⟨actual,objectEq⟩
  subst actual
  rw [laws.read]
  simp only [bind_ok]
  step as ⟨pages,pagesEq⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨pages,pagesEq,rfl⟩
end Itasca.Runtime.Interp

end
