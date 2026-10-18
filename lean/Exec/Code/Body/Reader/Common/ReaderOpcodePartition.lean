import Exec.Code.Body.Reader.Common.ReaderCompilerOrdinary
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
import Exec.Code.Local.Relations.Common.SliceOpcodes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The supported source-byte classification covers ordinary instructions,
structured openers/branches, and the two closing delimiters. -/
theorem SliceOpcode.partition {opcode : U8} (supported : SliceOpcode opcode) :
    opcode ∈ readerOrdinaryOpcodes ∨ ScopeOpcode opcode ∨ opcode = 5#u8 ∨ opcode = 11#u8 := by
  rcases supported.base_or_numeric with base | ⟨op, rfl⟩
  · simp only [SliceBaseOpcode, List.mem_cons, List.mem_nil_iff, or_false] at base
    rcases base with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · have equal : opcode = 0#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 1#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 5#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 11#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 15#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 16#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 26#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 32#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 33#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 34#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 65#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 66#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 69#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 70#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 73#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 80#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 81#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 84#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 106#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 107#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 124#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
    · have equal : opcode = 125#u8 := (UScalar.eq_equiv _ _).mpr h
      subst opcode
      simp [readerOrdinaryOpcodes, readerBaseOrdinaryOpcodes, ScopeOpcode]
  · left
    apply List.mem_append_right
    cases op with
    | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> decide
    | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> decide
    | unary ty operator => cases ty <;> cases operator <;> decide
    | eqz ty => cases ty <;> decide
    | conversion operator => cases operator <;> decide
end Exec.Code
