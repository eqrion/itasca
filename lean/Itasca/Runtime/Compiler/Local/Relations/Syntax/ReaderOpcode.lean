import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOpcode
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ExecutableTokens
import Itasca.Runtime.Compiler.Local.Source.SourceExecutableBody

/-!
Opcode bytes a body reader step can start with, grouped by the compiler entry
point that handles them. Both profiles share every family except the Wasm 2.0
extensions: table access, references, the `0xFC` prefix, SIMD and typed select.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Itasca.Runtime.Code

/-- Ordinary opcodes besides the integer numeric operators. Structured
openers, branches, `else` and `end` are handled by the source-zipper
dispatcher. -/
def readerBaseOrdinaryOpcodes : List U8 :=
  [0x00#u8, 0x01#u8, 0x0f#u8, 0x10#u8, 0x1a#u8, 0x20#u8, 0x21#u8, 0x22#u8,
   0x41#u8, 0x42#u8, 0x45#u8, 0x46#u8, 0x49#u8, 0x50#u8, 0x51#u8, 0x54#u8,
   0x6a#u8, 0x6b#u8, 0x7c#u8, 0x7d#u8]

def readerOrdinaryOpcodes : List U8 := readerBaseOrdinaryOpcodes ++ integerOpcodes

/-- Structured openers and branches. -/
def ScopeOpcode (opcode : U8) : Prop := opcode.val ∈ [2, 3, 4, 12, 13]

/-- Untyped select, global access, float constants, and memory loads and stores. -/
def scalarOpcodeValues : List Nat :=
  [27, 35, 36, 67, 68, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58,
   59, 60, 61, 62]

/-- Unprefixed float operators. -/
def floatBaseOpcodeValues : List Nat :=
  [139, 140, 141, 142, 143, 144, 145, 153, 154, 155, 156, 157, 158, 159, 146, 147, 148, 149, 150,
   151, 152, 160, 161, 162, 163, 164, 165, 166, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102,
   178, 179, 183, 184, 180, 181, 185, 186, 168, 169, 174, 175, 170, 171, 176, 177, 188, 189, 190,
   191, 187, 182]

theorem float_base_opcode_of_mem {opcode : U8} (member : opcode.val ∈ floatBaseOpcodeValues) :
    ∃ op : Abs.Float.Instruction, (floatOpcode op).val < 256 ∧ UScalar.cast .U8 (floatOpcode op) = opcode := by
  simp only [floatBaseOpcodeValues,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨.unary .F32 .ABS,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .NEG,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .CEIL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .FLOOR,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .TRUNC,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .NEAREST,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .SQRT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .ABS,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .NEG,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .CEIL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .FLOOR,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .TRUNC,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .NEAREST,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .SQRT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .ADD,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .SUB,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MUL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .DIV,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MIN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MAX,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .COPYSIGN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .ADD,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .SUB,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MUL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .DIV,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MIN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MAX,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .COPYSIGN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .EQ,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .NE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .LT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .GT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .LE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .GE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .EQ,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .NE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .LT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .GT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .LE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .GE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F32 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F32 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F64 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F64 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F32 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F32 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F64 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F64 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I32 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I32 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I64 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I64 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I32 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I32 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I64 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I64 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretFloat .F32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretFloat .F64,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretInt .I32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretInt .I64,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.promote,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.demote,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

/-- The opcode families a successful reader step under `profile` starts
with, one constructor per compiler entry point. -/
inductive ReaderOpcode : ValidationProfile → U8 → Prop where
  | ordinary {profile opcode} : opcode ∈ readerOrdinaryOpcodes → ReaderOpcode profile opcode
  | scope {profile opcode} : ScopeOpcode opcode → ReaderOpcode profile opcode
  | else_ {profile opcode} : opcode = 5#u8 → ReaderOpcode profile opcode
  | end_ {profile opcode} : opcode = 11#u8 → ReaderOpcode profile opcode
  | scalar {profile opcode} : opcode.val ∈ scalarOpcodeValues → ReaderOpcode profile opcode
  | float {profile opcode} : opcode.val ∈ floatBaseOpcodeValues → ReaderOpcode profile opcode
  | memory {profile opcode} : opcode.val ∈ [63, 64] → ReaderOpcode profile opcode
  | callIndirect {profile opcode} : opcode = 17#u8 → ReaderOpcode profile opcode
  | brTable {profile opcode} : opcode = 14#u8 → ReaderOpcode profile opcode
  | stateful {opcode} : opcode.val ∈ [37, 38, 208, 209, 210] → ReaderOpcode .Wasm2 opcode
  | misc {opcode} : opcode = 252#u8 → ReaderOpcode .Wasm2 opcode
  | simd {opcode} : opcode = 253#u8 → ReaderOpcode .Wasm2 opcode
  | typedSelect {opcode} : opcode = 28#u8 → ReaderOpcode .Wasm2 opcode

/-- The Wasm 2.0 stateful entry point also handles `memory.size` and `memory.grow`. -/
theorem stateful_opcode_values {opcode : U8}
    (h : opcode.val ∈ [63, 64] ∨ opcode.val ∈ [37, 38, 208, 209, 210]) :
    opcode.val ∈ [37, 38, 63, 64, 208, 209, 210] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  omega

theorem ReaderOpcode.wasm2 {profile opcode} : ReaderOpcode profile opcode → ReaderOpcode .Wasm2 opcode
  | .ordinary h => .ordinary h | .scope h => .scope h | .else_ h => .else_ h | .end_ h => .end_ h
  | .scalar h => .scalar h | .float h => .float h | .memory h => .memory h
  | .callIndirect h => .callIndirect h | .brTable h => .brTable h | .stateful h => .stateful h
  | .misc h => .misc h | .simd h => .simd h | .typedSelect h => .typedSelect h

/-- Closes `ReaderOpcode profile opcode` for a concrete opcode byte. -/
macro "reader_opcode" : tactic => `(tactic| first
  | exact .ordinary (by clear * -; decide +revert) | exact .scope (by clear * -; unfold ScopeOpcode; decide +revert)
  | exact .else_ (by clear * -; decide +revert) | exact .end_ (by clear * -; decide +revert)
  | exact .scalar (by clear * -; decide +revert) | exact .float (by clear * -; decide +revert)
  | exact .memory (by clear * -; decide +revert) | exact .callIndirect (by clear * -; decide +revert)
  | exact .brTable (by clear * -; decide +revert) | exact .stateful (by clear * -; decide +revert)
  | exact .misc (by clear * -; decide +revert) | exact .simd (by clear * -; decide +revert)
  | exact .typedSelect (by clear * -; decide +revert))

/-- Closes the goals left by splitting a match on `opcode.val`. -/
macro "reader_opcode_cases " opcode:ident : tactic => `(tactic| all_goals
  rename_i value
  rcases $opcode:ident with ⟨⟨n, bound⟩⟩
  change n = _ at value
  subst value
  reader_opcode)

set_option maxHeartbeats 2000000 in
theorem numeric_reader_opcode {profile opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation) : ReaderOpcode profile opcode := by
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  reader_opcode_cases opcode

theorem memory_reader_opcode {profile opcode operation}
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) : ReaderOpcode profile opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  reader_opcode_cases opcode

set_option maxHeartbeats 2000000 in
theorem sign_reader_opcode {profile opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation) :
    ReaderOpcode profile opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  reader_opcode_cases opcode

theorem wasm1_immediate_reader_opcode {profile opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) : ReaderOpcode profile opcode := by
  cases encoded
  all_goals first
    | reader_opcode
    | exact numeric_reader_opcode (by assumption)
    | exact memory_reader_opcode (by assumption)

theorem wasm2_immediate_reader_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) : ReaderOpcode .Wasm2 opcode := by
  cases encoded with
  | plain encoded => exact wasm1_immediate_reader_opcode encoded
  | signExtension _ _ meaning => exact sign_reader_opcode meaning
  | reference encoded => cases encoded <;> reader_opcode
  | _ => reader_opcode

end Itasca.Runtime.Code

namespace Itasca.Wasm2
theorem At.reader_opcode {data start token next}
    (encoded : At data start token next) (inbounds : start.val < data.length) :
    Itasca.Runtime.Code.ReaderOpcode .Wasm2 data.val[start.val] := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using head
  rw [equal]
  exact Itasca.Runtime.Code.wasm2_immediate_reader_opcode grammar

theorem BodyEncoding.next_reader_opcode {data body tokens position}
    (encoded : BodyEncoding data body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Itasca.Runtime.Code.ReaderOpcode .Wasm2 data.val[position.val] := by
  obtain ⟨token,next,atToken,_⟩ := encoded.next_executable_token (Itasca.Runtime.Code.SourceExecutable.body_wasm2 encoded) before remaining
  exact atToken.reader_opcode remaining
end Itasca.Wasm2
