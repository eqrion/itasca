import Itasca.Results.Definitions.Binary

namespace Itasca.Binary
open Aeneas.Std

theorem Leb128.encoding_iff (bytes : List U8) (value : Nat) :
    Leb128.Encoding bytes value ↔
      WebAssembly.Binary.Leb128.U32Encoding (bytes.map sourceByte) value := by
  rw [WebAssembly.Binary.Leb128.U32Encoding, WebAssembly.Binary.Leb128.unsigned_map]
  rfl

theorem SignedLeb.encoding_iff (format : SignedLeb.Format) (bytes : List U8) (value : Int) :
    SignedLeb.Encoding format bytes value ↔ WebAssembly.Binary.Leb128.SignedWith
      UInt8.toNat format.last.val format.lower.val format.upper.val (bytes.map sourceByte) value := by
  rw [WebAssembly.Binary.Leb128.signed_map]
  rfl

theorem SignedLeb32.encoding_iff (bytes : List U8) (value : Int) :
    SignedLeb32.Encoding bytes value ↔ WebAssembly.Binary.Leb128.S32Encoding
      (bytes.map sourceByte) value := SignedLeb.encoding_iff _ _ _

theorem SignedLeb33.encoding_iff (bytes : List U8) (value : Int) :
    SignedLeb33.Encoding bytes value ↔ WebAssembly.Binary.Leb128.S33Encoding
      (bytes.map sourceByte) value := SignedLeb.encoding_iff _ _ _

theorem SignedLeb64.encoding_iff (bytes : List U8) (value : Int) :
    SignedLeb64.Encoding bytes value ↔ WebAssembly.Binary.Leb128.S64Encoding
      (bytes.map sourceByte) value := SignedLeb.encoding_iff _ _ _

end Itasca.Binary
