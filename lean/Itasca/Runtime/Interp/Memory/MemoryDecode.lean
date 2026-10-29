import Itasca.Runtime.Interp.Memory.MemoryEncoding
import Itasca.Runtime.Spec.MemoryLoad
import Itasca.Runtime.Spec.SegmentCopySlice
import Itasca.Runtime.Spec.MemoryStore
import Itasca.Runtime.Representation.Collection

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

def numericMemoryType : numtype → Itasca.types.ValueType
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
