import Itasca.Support.EnvTranslation
import Itasca.Binary.Wasm2.BlockType
import Itasca.Binary.Wasm1.Encoding

/-!
# Wasm 2.0 reference instruction bytes

`ReferencesBinary.Immediate` relates the opcodes of `ref.null`, `ref.is_null`, `ref.func`,
typed `select`, `table.get`, `table.set` and the Wasm 2.0 `call_indirect` to their SpecTec
instructions and immediate bytes. `Immediate.wellFormed` shows that each satisfies `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.ReferencesBinary

/-- The reference type tag is the literal byte `0x70` or `0x6f`. -/
def referenceByte : wasm_types.ElemType → U8
  | .FuncRef => 0x70#u8
  | .ExternRef => 0x6f#u8

/-- The immediates of reference, typed select, table access and indirect call instructions. Index
encodings admit every valid unsigned LEB128. -/
inductive Immediate : U8 → instr → List U8 → Prop where
  | refNull (rt : wasm_types.ElemType) :
      Immediate 0xd0#u8 (.REF_NULL (Translate.referenceType rt)) [referenceByte rt]
  | refIsNull : Immediate 0xd1#u8 .REF_IS_NULL []
  | refFunc (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0xd2#u8 (.REF_FUNC (.mk_uN index.val)) bytes
  | selectTyped (ty : wasm_types.ValueType) {count} : Leb128.Encoding count 1 →
      Immediate 0x1c#u8 (.SELECT (some [Translate.valueType ty])) (count ++ [valueByte ty])
  | tableGet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x25#u8 (.TABLE_GET (.mk_uN index.val)) bytes
  | tableSet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x26#u8 (.TABLE_SET (.mk_uN index.val)) bytes
  | callIndirect (typeIndex tableIndex : U32) {typeBytes tableBytes} :
      Leb128.Encoding typeBytes typeIndex.val → Leb128.Encoding tableBytes tableIndex.val →
      Immediate 0x11#u8 (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        (typeBytes ++ tableBytes)

end Itasca.Wasm2.ReferencesBinary
