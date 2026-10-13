import Itasca.Support.EnvTranslation
import Itasca.Binary.Wasm2.BlockType
import Itasca.Binary.Wasm1.Encoding

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.ReferencesBinary

/-- Core 2.0 reference-type tags are literal bytes, not padded heap types. -/
def referenceByte : types.ElemType → U8
  | .FuncRef => 0x70#u8
  | .ExternRef => 0x6f#u8

/-- Independent encoding of reference, typed-select, table access, and indexed
indirect-call immediates. Index encodings admit every valid unsigned LEB. -/
inductive Immediate : U8 → instr → List U8 → Prop where
  | refNull (rt : types.ElemType) :
      Immediate 0xd0#u8 (.REF_NULL (Translate.referenceType rt)) [referenceByte rt]
  | refIsNull : Immediate 0xd1#u8 .REF_IS_NULL []
  | refFunc (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0xd2#u8 (.REF_FUNC (.mk_uN index.val)) bytes
  | selectTyped (ty : types.ValueType) {count} : Leb128.Encoding count 1 →
      Immediate 0x1c#u8 (.SELECT (some [Translate.valueType ty])) (count ++ [valueByte ty])
  | tableGet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x25#u8 (.TABLE_GET (.mk_uN index.val)) bytes
  | tableSet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x26#u8 (.TABLE_SET (.mk_uN index.val)) bytes
  | callIndirect (typeIndex tableIndex : U32) {typeBytes tableBytes} :
      Leb128.Encoding typeBytes typeIndex.val → Leb128.Encoding tableBytes tableIndex.val →
      Immediate 0x11#u8 (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        (typeBytes ++ tableBytes)

theorem Immediate.wellFormed {opcode op bytes} (h : Immediate opcode op bytes) : wf_instr op := by
  cases h with
  | refNull rt => exact .instr_case_40 _
  | refIsNull => exact .instr_case_42
  | refFunc i _ => exact .instr_case_41 _ (EnvTranslation.index_wf i)
  | selectTyped _ _ => exact .instr_case_3 _
  | tableGet i _ => exact .instr_case_48 _ (EnvTranslation.index_wf i)
  | tableSet i _ => exact .instr_case_49 _ (EnvTranslation.index_wf i)
  | callIndirect ti table _ _ =>
      exact .instr_case_11 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf ti)

end Itasca.MultiValue.ReferencesBinary
