import Itasca.Support.EnvTranslation
import Itasca.Binary.Wasm1.Encoding

/-!
# Wasm 2.0 bulk memory and table bytes

`BulkBinary.Immediate` relates the `0xfc` subopcodes 8 to 17 (`memory.init` through
`table.fill`) to their SpecTec instructions and immediate bytes. `Immediate.wellFormed` shows
that each satisfies `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.BulkBinary

/-- The immediates of bulk memory and table instructions after their `0xfc` subopcode. Memory
indices are reserved literal zero bytes. -/
inductive Immediate : U32 → instr → List U8 → Prop where
  | memoryInit (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 8#u32 (.MEMORY_INIT (.mk_uN index.val)) (bytes ++ [0#u8])
  | dataDrop (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 9#u32 (.DATA_DROP (.mk_uN index.val)) bytes
  | memoryCopy : Immediate 10#u32 .MEMORY_COPY [0#u8, 0#u8]
  | memoryFill : Immediate 11#u32 .MEMORY_FILL [0#u8]
  | tableInit (element table : U32) {elementBytes tableBytes} :
      Leb128.Encoding elementBytes element.val → Leb128.Encoding tableBytes table.val →
      Immediate 12#u32 (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
        (elementBytes ++ tableBytes)
  | elemDrop (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 13#u32 (.ELEM_DROP (.mk_uN index.val)) bytes
  | tableCopy (destination source : U32) {destinationBytes sourceBytes} :
      Leb128.Encoding destinationBytes destination.val → Leb128.Encoding sourceBytes source.val →
      Immediate 14#u32 (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
        (destinationBytes ++ sourceBytes)
  | tableGrow (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 15#u32 (.TABLE_GROW (.mk_uN index.val)) bytes
  | tableSize (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 16#u32 (.TABLE_SIZE (.mk_uN index.val)) bytes
  | tableFill (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 17#u32 (.TABLE_FILL (.mk_uN index.val)) bytes

/-- Every bulk instruction spelled by `Immediate` is well formed. -/
theorem Immediate.wellFormed {subopcode op bytes} (h : Immediate subopcode op bytes) : wf_instr op := by
  cases h with
  | memoryInit i _ => exact .instr_case_66 _ (EnvTranslation.index_wf i)
  | dataDrop i _ => exact .instr_case_67 _ (EnvTranslation.index_wf i)
  | memoryCopy => exact .instr_case_65
  | memoryFill => exact .instr_case_64
  | tableInit element table _ _ =>
      exact .instr_case_54 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf element)
  | elemDrop i _ => exact .instr_case_55 _ (EnvTranslation.index_wf i)
  | tableCopy destination source _ _ =>
      exact .instr_case_53 _ _ (EnvTranslation.index_wf destination) (EnvTranslation.index_wf source)
  | tableGrow i _ => exact .instr_case_51 _ (EnvTranslation.index_wf i)
  | tableSize i _ => exact .instr_case_50 _ (EnvTranslation.index_wf i)
  | tableFill i _ => exact .instr_case_52 _ (EnvTranslation.index_wf i)

/-- Bulk subopcodes lie between 8 and 17. -/
theorem Immediate.subopcode_range {subopcode op bytes} (h : Immediate subopcode op bytes) :
    8 ≤ subopcode.val ∧ subopcode.val ≤ 17 := by
  cases h <;> decide

end Itasca.Wasm2.BulkBinary
