import Itasca.Runtime.Interp.Memory.MemoryStoreEncoding
import Itasca.Runtime.Interp.Memory.MemoryLoadSource
import Itasca.Runtime.Spec.MemoryStore

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

theorem numericStoreValue_decodes (ty : numtype) (word : U64) :
    Store.decodeWords (numericMemoryType ty) word 0#u64 = .CONST ty (numericStoreValue ty word) := by
  cases ty <;> rfl

theorem numericStoreValue_bytes (ty : numtype) (word : U64) :
    nbytes_ ty (numericStoreValue ty word) = Builtins.integerBytes (Spec.scalarNumBytes ty) word.val := by
  cases ty
  · simpa [nbytes_,numericStoreValue,ibytes_,proj_uN_0,Spec.scalarNumBytes] using Spec.integerBytes_mod 4 word.val
  · rfl
  · have bits := Builtins.Float.float_bits_roundtrip_32 (word.val % 2^32) (Nat.mod_lt _ (by norm_num))
    change Builtins.integerBytes 4 (Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))) = _
    rw [bits]
    exact Spec.integerBytes_mod 4 word.val
  · have bits := Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)
    simp [nbytes_,numericStoreValue,fbytes_,bits,Spec.scalarNumBytes]

end Itasca.Runtime.Interp
