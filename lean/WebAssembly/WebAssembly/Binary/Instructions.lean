import WebAssembly.Binary.Memory
import WebAssembly.Binary.Opcodes

namespace WebAssembly.Binary

/-- A flat instruction stream element: a plain instruction, a structured instruction header or
`else` or `end`. Block headers retain their SpecTec block type. -/
inductive TokenWith (τ : Type) where
  | plain (op : instr)
  | block (bt : τ)
  | loop (bt : τ)
  | if_ (bt : τ)
  | else_ | end_

/-- A plain token spells a well-formed instruction. The binary relation `Immediate` restricts
which plain tokens occur. -/
inductive SimpleWith {τ : Type} : TokenWith τ → instr → Prop where
  | plain (op : instr) : wf_instr op → SimpleWith (.plain op) op

/-- A flat token list spells a list of SpecTec instructions. An `if` with an empty else branch has
two spellings, with and without `else`. -/
inductive EmitsWith {τ : Type} (toSpec : τ → blocktype) : List (TokenWith τ) → List instr → Prop where
  | nil : EmitsWith toSpec [] []
  | simple {tokens ops token op} : EmitsWith toSpec tokens ops → SimpleWith token op →
      EmitsWith toSpec (tokens ++ [token]) (ops ++ [op])
  | block {tokens ops bodyTokens body} (bt : τ) :
      EmitsWith toSpec tokens ops → EmitsWith toSpec bodyTokens body →
      EmitsWith toSpec (tokens ++ [.block bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.BLOCK (toSpec bt) body])
  | loop {tokens ops bodyTokens body} (bt : τ) :
      EmitsWith toSpec tokens ops → EmitsWith toSpec bodyTokens body →
      EmitsWith toSpec (tokens ++ [.loop bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.LOOP (toSpec bt) body])
  | ifElse {tokens ops thenTokens thenOps elseTokens elseOps} (bt : τ) :
      EmitsWith toSpec tokens ops → EmitsWith toSpec thenTokens thenOps → EmitsWith toSpec elseTokens elseOps →
      EmitsWith toSpec (tokens ++ [.if_ bt] ++ thenTokens ++ [.else_] ++ elseTokens ++ [.end_])
        (ops ++ [.IFELSE (toSpec bt) thenOps elseOps])
  | ifEnd {tokens ops bodyTokens body} (bt : τ) :
      EmitsWith toSpec tokens ops → EmitsWith toSpec bodyTokens body →
      EmitsWith toSpec (tokens ++ [.if_ bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.IFELSE (toSpec bt) body []])

/-- A function body: tokens that spell the instructions, followed by the final `end`. -/
def BodyTokensWith {τ : Type} (toSpec : τ → blocktype) (tokens : List (TokenWith τ)) (ops : List instr) : Prop :=
  ∃ inner, tokens = inner ++ [.end_] ∧ EmitsWith toSpec inner ops

abbrev Token := TokenWith blocktype
abbrev Simple := @SimpleWith blocktype
abbrev Emits := EmitsWith id
abbrev BodyTokens := BodyTokensWith id

def emptyBlockByte : UInt8 := 0x40

inductive ScalarBlockByteWith {τ β : Type} (empty : τ) (value : ValueType → τ) (byte : UInt8 → β) :
    τ → β → Prop where
  | empty : ScalarBlockByteWith empty value byte empty (byte emptyBlockByte)
  | i32 : ScalarBlockByteWith empty value byte (value .I32) (byte (valueByte .I32))
  | i64 : ScalarBlockByteWith empty value byte (value .I64) (byte (valueByte .I64))
  | f32 : ScalarBlockByteWith empty value byte (value .F32) (byte (valueByte .F32))
  | f64 : ScalarBlockByteWith empty value byte (value .F64) (byte (valueByte .F64))

inductive BlockEncoding : blocktype → List UInt8 → Prop where
  | empty : BlockEncoding (._RESULT none) [emptyBlockByte]
  | result (ty : ValueType) : BlockEncoding (._RESULT (some ty.toSpec)) [valueByte ty]
  | index (i : Nat) {bytes} : Leb128.S33Encoding bytes i → BlockEncoding (._IDX (.mk_uN i)) bytes

theorem BlockEncoding.empty_iff {bs} : BlockEncoding (._RESULT none) bs ↔ bs = [emptyBlockByte] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .empty

theorem BlockEncoding.result_iff (t : ValueType) {bs} :
    BlockEncoding (._RESULT (some t.toSpec)) bs ↔ bs = [valueByte t] := by
  constructor
  · intro h
    generalize hv : t.toSpec = v at h
    cases h with
    | result u =>
      have eq : t = u := by cases t <;> cases u <;> first | rfl | contradiction
      subst u; rfl
  · rintro rfl; exact .result t

theorem BlockEncoding.index_iff (n : Nat) {bs} :
    BlockEncoding (._IDX (.mk_uN n)) bs ↔ Leb128.S33Encoding bs n := by
  constructor
  · intro h; cases h; assumption
  · exact .index n

namespace Scalar
/-- Integer representations and opcode tables used by the scalar immediate grammar. -/
structure Operands (Byte Index Signed32 Signed64 Word64 Arg Row Block : Type) where
  byte : UInt8 → Byte
  index : Index → Nat
  int32 : Signed32 → Int
  int64 : Signed64 → Int
  word64 : Word64 → Nat
  align : Arg → Nat
  offset : Arg → Nat
  memory : Byte → Option Row
  instruction : Row → Arg → instr
  numeric : Byte → Option instr
  blockByte : Block → Byte → Prop
  leb : List Byte → Nat → Prop
  s32 : List Byte → Int → Prop
  s64 : List Byte → Int → Prop
  float : Nat → List Byte → Nat → Prop

inductive IndicesEncodingWith {ι β : Type} (index : ι → Nat) (leb : List β → Nat → Prop) :
    List ι → List β → Prop where
  | nil : IndicesEncodingWith index leb [] []
  | cons {i xs first rest} : leb first (index i) → IndicesEncodingWith index leb xs rest →
      IndicesEncodingWith index leb (i :: xs) (first ++ rest)

inductive ImmediateWith {Byte Index Signed32 Signed64 Word64 Arg Row Block : Type} (r : Operands Byte Index Signed32 Signed64 Word64 Arg Row Block) : Byte → TokenWith Block → List Byte → Prop where
  | unreachable : ImmediateWith r (r.byte 0x00) (.plain .UNREACHABLE) []
  | nop : ImmediateWith r (r.byte 0x01) (.plain .NOP) []
  | block {bt b} : r.blockByte bt b → ImmediateWith r (r.byte 0x02) (.block bt) [b]
  | loop {bt b} : r.blockByte bt b → ImmediateWith r (r.byte 0x03) (.loop bt) [b]
  | if_ {bt b} : r.blockByte bt b → ImmediateWith r (r.byte 0x04) (.if_ bt) [b]
  | else_ : ImmediateWith r (r.byte 0x05) .else_ []
  | end_ : ImmediateWith r (r.byte 0x0B) .end_ []
  | br (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x0C) (.plain (.BR (.mk_uN (r.index idx)))) bytes
  | brIf (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x0D) (.plain (.BR_IF (.mk_uN (r.index idx)))) bytes
  | brTable (indices : List Index) (default : Index) {count entries final} :
      r.leb count indices.length → IndicesEncodingWith r.index r.leb indices entries →
      r.leb final (r.index default) →
      ImmediateWith r (r.byte 0x0E) (.plain (.BR_TABLE (indices.map (fun i => .mk_uN (r.index i))) (.mk_uN (r.index default))))
        (count ++ entries ++ final)
  | return_ : ImmediateWith r (r.byte 0x0F) (.plain .RETURN) []
  | call (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x10) (.plain (.CALL (.mk_uN (r.index idx)))) bytes
  | callIndirect (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x11) (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN (r.index idx)))) (bytes ++ [r.byte 0])
  | drop : ImmediateWith r (r.byte 0x1A) (.plain .DROP) []
  | select : ImmediateWith r (r.byte 0x1B) (.plain (.SELECT none)) []
  | localGet (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x20) (.plain (.LOCAL_GET (.mk_uN (r.index idx)))) bytes
  | localSet (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x21) (.plain (.LOCAL_SET (.mk_uN (r.index idx)))) bytes
  | localTee (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x22) (.plain (.LOCAL_TEE (.mk_uN (r.index idx)))) bytes
  | globalGet (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x23) (.plain (.GLOBAL_GET (.mk_uN (r.index idx)))) bytes
  | globalSet (idx : Index) {bytes} : r.leb bytes (r.index idx) →
      ImmediateWith r (r.byte 0x24) (.plain (.GLOBAL_SET (.mk_uN (r.index idx)))) bytes
  | memory (opcode : Byte) (operation : Row) (arg : Arg)
      {alignment offset} (meaning : r.memory opcode = some operation) :
      r.leb alignment (r.align arg) → r.leb offset (r.offset arg) →
      ImmediateWith r opcode (.plain (r.instruction operation arg)) (alignment ++ offset)
  | memorySize : ImmediateWith r (r.byte 0x3F) (.plain .MEMORY_SIZE) [r.byte 0]
  | memoryGrow : ImmediateWith r (r.byte 0x40) (.plain .MEMORY_GROW) [r.byte 0]
  | i32Const (value : Signed32) {bytes} : r.s32 bytes (r.int32 value) →
      ImmediateWith r (r.byte 0x41) (.plain (Constants.i32Const (r.int32 value))) bytes
  | i64Const (value : Signed64) {bytes} : r.s64 bytes (r.int64 value) →
      ImmediateWith r (r.byte 0x42) (.plain (Constants.i64 (r.int64 value))) bytes
  | f32Const (bits : Index) {bytes} : r.float 4 bytes (r.index bits) →
      ImmediateWith r (r.byte 0x43) (.plain (Constants.f32 (r.index bits))) bytes
  | f64Const (bits : Word64) {bytes} : r.float 8 bytes (r.word64 bits) →
      ImmediateWith r (r.byte 0x44) (.plain (Constants.f64 (r.word64 bits))) bytes
  | numericInstruction (opcode : Byte) (source : instr)
      (meaning : r.numeric opcode = some source) :
      ImmediateWith r opcode (.plain source) []

abbrev nativeOperands : Operands UInt8 Nat Int Int Nat (Nat × Nat) MemoryMeaning.Operation blocktype where
  byte := id
  index := id
  int32 := id
  int64 := id
  word64 := id
  align := Prod.fst
  offset := Prod.snd
  memory := MemoryMeaning.opcodeMeaning
  instruction := fun row arg => row.op ⟨.mk_uN arg.1, .mk_uN arg.2⟩
  numeric := Numeric.opcodeInstruction
  blockByte := ScalarBlockByteWith (._RESULT none) (fun t => ._RESULT (some t.toSpec)) id
  leb := Leb128.U32Encoding
  s32 := Leb128.S32Encoding
  s64 := Leb128.S64Encoding
  float := FloatBits.Encoding

abbrev IndicesEncoding := IndicesEncodingWith id Leb128.U32Encoding

abbrev Immediate (opcode : UInt8) (op : instr) := ImmediateWith nativeOperands opcode (.plain op)

end Scalar

namespace BulkBinary

/-- The immediates of bulk memory and table instructions after their `0xfc` subopcode. Memory
indices are reserved literal zero bytes. -/
inductive ImmediateWith {ι β : Type} (index : ι → Nat) (opcode : UInt32 → ι)
    (byte : UInt8 → β) (leb : List β → Nat → Prop) : ι → instr → List β → Prop where
  | memoryInit (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 8) (.MEMORY_INIT (.mk_uN (index i))) (bytes ++ [byte 0])
  | dataDrop (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 9) (.DATA_DROP (.mk_uN (index i))) bytes
  | memoryCopy : ImmediateWith index opcode byte leb (opcode 10) .MEMORY_COPY [byte 0, byte 0]
  | memoryFill : ImmediateWith index opcode byte leb (opcode 11) .MEMORY_FILL [byte 0]
  | tableInit (element table : ι) {elementBytes tableBytes} :
      leb elementBytes (index element) → leb tableBytes (index table) →
      ImmediateWith index opcode byte leb (opcode 12) (.TABLE_INIT (.mk_uN (index table)) (.mk_uN (index element)))
        (elementBytes ++ tableBytes)
  | elemDrop (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 13) (.ELEM_DROP (.mk_uN (index i))) bytes
  | tableCopy (destination source : ι) {destinationBytes sourceBytes} :
      leb destinationBytes (index destination) → leb sourceBytes (index source) →
      ImmediateWith index opcode byte leb (opcode 14) (.TABLE_COPY (.mk_uN (index destination)) (.mk_uN (index source)))
        (destinationBytes ++ sourceBytes)
  | tableGrow (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 15) (.TABLE_GROW (.mk_uN (index i))) bytes
  | tableSize (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 16) (.TABLE_SIZE (.mk_uN (index i))) bytes
  | tableFill (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith index opcode byte leb (opcode 17) (.TABLE_FILL (.mk_uN (index i))) bytes

abbrev Immediate := ImmediateWith id UInt32.toNat id Leb128.U32Encoding

end BulkBinary

namespace ReferencesBinary

/-- The reference type tag is the literal byte `0x70` or `0x6f`. -/
def referenceByte : reftype → UInt8
  | .FUNCREF => 0x70
  | .EXTERNREF => 0x6f

/-- The immediates of reference, typed select, table access and indirect call instructions. Index
encodings admit every valid unsigned LEB128. -/
inductive ImmediateWith {β ι ρ τ : Type} (byte : UInt8 → β) (index : ι → Nat)
    (ref : ρ → reftype) (val : τ → valtype) (tag : τ → β) (leb : List β → Nat → Prop) :
    β → instr → List β → Prop where
  | refNull (rt : ρ) :
      ImmediateWith byte index ref val tag leb (byte 0xd0) (.REF_NULL (ref rt)) [byte (referenceByte (ref rt))]
  | refIsNull : ImmediateWith byte index ref val tag leb (byte 0xd1) .REF_IS_NULL []
  | refFunc (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith byte index ref val tag leb (byte 0xd2) (.REF_FUNC (.mk_uN (index i))) bytes
  | selectTyped (ty : τ) {count} : leb count 1 →
      ImmediateWith byte index ref val tag leb (byte 0x1c) (.SELECT (some [val ty])) (count ++ [tag ty])
  | tableGet (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith byte index ref val tag leb (byte 0x25) (.TABLE_GET (.mk_uN (index i))) bytes
  | tableSet (i : ι) {bytes} : leb bytes (index i) →
      ImmediateWith byte index ref val tag leb (byte 0x26) (.TABLE_SET (.mk_uN (index i))) bytes
  | callIndirect (typeIndex tableIndex : ι) {typeBytes tableBytes} :
      leb typeBytes (index typeIndex) → leb tableBytes (index tableIndex) →
      ImmediateWith byte index ref val tag leb (byte 0x11) (.CALL_INDIRECT (.mk_uN (index tableIndex)) (.mk_uN (index typeIndex)))
        (typeBytes ++ tableBytes)

abbrev Immediate := ImmediateWith id id id ValueType.toSpec valueByte Leb128.U32Encoding

end ReferencesBinary

namespace Simd
/-- A `v128.const` of 128 immediate bits, given as two little-endian 64-bit halves. -/
def vectorConstant (low high : Nat) : instr :=
  .VCONST .V128 (.mk_uN (low + high * 2 ^ 64))

/-- The first `count` little-endian bytes of a natural number. -/
def unpackBytes (bits : Nat) (count : Nat) : List Nat :=
  match count with
  | 0 => []
  | n + 1 => bits % 256 :: unpackBytes (bits / 256) n

/-- The sixteen lane indices of an `i8x16.shuffle`, from the bytes of its two 64-bit halves. -/
def shuffleIndices (low high : Nat) : List laneidx :=
  ((unpackBytes low 8) ++ (unpackBytes high 8)).map uN.mk_uN

/-- An `i8x16.shuffle` with the lane indices of the two halves. -/
def shuffle (low high : Nat) : instr :=
  .VSHUFFLE (.mk_ishape (.X .I8 (.mk_dim 16))) (shuffleIndices low high)

/-- Conversion of immediate operands into the integer and memory-argument values used by Wasm. -/
structure Operands (β ι μ ω : Type) where
  lane : β → Nat
  opcode : UInt32 → ι
  subopcode : ι → Nat
  alignment : μ → Nat
  offset : μ → Nat
  bits : ω → Nat
  leb : List β → Nat → Prop
  fixed64 : List β → Nat → Prop

def Operands.memArg (rep : Operands β ι μ ω) (arg : μ) : memarg :=
  ⟨.mk_uN (rep.alignment arg), .mk_uN (rep.offset arg)⟩

/-- Bytes following a SIMD subopcode. The enclosing instruction supplies the prefix. -/
inductive ImmediateWith {β ι μ ω : Type} (rep : Operands β ι μ ω) : ι → instr → List β → Prop where
  | pure (opcode : ι) (op : instr) : pureInstruction (rep.subopcode opcode) = some op →
      ImmediateWith rep opcode op []
  | lane (opcode : ι) (op : LaneOperation) (lane : β) : laneMeaning (rep.subopcode opcode) = some op →
      ImmediateWith rep opcode (op.instruction (.mk_uN (rep.lane lane))) [lane]
  | memory (opcode : ι) (op : MemoryOperation) (arg : μ) {align offset} :
      memoryMeaning (rep.subopcode opcode) = some op → op.laneCount = 0 →
      rep.leb align (rep.alignment arg) → rep.leb offset (rep.offset arg) →
      ImmediateWith rep opcode (op.instruction (rep.memArg arg) (.mk_uN 0)) (align ++ offset)
  | memoryLane (opcode : ι) (op : MemoryOperation) (arg : μ) (lane : β) {align offset} :
      memoryMeaning (rep.subopcode opcode) = some op → op.laneCount ≠ 0 →
      rep.leb align (rep.alignment arg) → rep.leb offset (rep.offset arg) →
      ImmediateWith rep opcode (op.instruction (rep.memArg arg) (.mk_uN (rep.lane lane))) (align ++ offset ++ [lane])
  | constant (low high : ω) {lower upper} : rep.fixed64 lower (rep.bits low) → rep.fixed64 upper (rep.bits high) →
      ImmediateWith rep (rep.opcode 12) (vectorConstant (rep.bits low) (rep.bits high)) (lower ++ upper)
  | shuffle (low high : ω) {lower upper} : rep.fixed64 lower (rep.bits low) → rep.fixed64 upper (rep.bits high) →
      ImmediateWith rep (rep.opcode 13) (Simd.shuffle (rep.bits low) (rep.bits high)) (lower ++ upper)

abbrev nativeOperands : Operands UInt8 Nat (Nat × Nat) Nat :=
  ⟨UInt8.toNat, UInt32.toNat, id, Prod.fst, Prod.snd, id, Leb128.U32Encoding, FloatBits.Encoding 8⟩

abbrev Immediate := ImmediateWith nativeOperands

end Simd

/-- Component grammars used to assemble the complete instruction from its opcode and operands. -/
structure InstructionOperands (β ι τ : Type) where
  byte : UInt8 → β
  index : ι → Nat
  scalar : β → instr → List β → Prop
  sign : β → Option instr
  saturating : ι → Option instr
  reference : β → instr → List β → Prop
  bulk : ι → instr → List β → Prop
  simd : ι → instr → List β → Prop
  block : τ → List β → Prop
  leb : List β → Nat → Prop

inductive ImmediateWith {β ι τ : Type} (r : InstructionOperands β ι τ) : β → TokenWith τ → List β → Prop where
  | plain {opcode op bytes} : r.scalar opcode op bytes →
      ImmediateWith r opcode (.plain op) bytes
  | signExtensionInstruction (opcode : β) (source : instr) :
      r.sign opcode = some source →
      ImmediateWith r opcode (.plain source) []
  | saturatingInstruction (subopcode : ι) (source : instr) {bytes} :
      r.saturating subopcode = some source →
      r.leb bytes (r.index subopcode) → ImmediateWith r (r.byte 0xFC) (.plain source) bytes
  | reference {opcode op bytes} : r.reference opcode op bytes →
      ImmediateWith r opcode (.plain op) bytes
  | bulk (subopcode : ι) {prefixBytes op bytes} : r.leb prefixBytes (r.index subopcode) →
      r.bulk subopcode op bytes → ImmediateWith r (r.byte 0xfc) (.plain op) (prefixBytes ++ bytes)
  | simd (subopcode : ι) {prefixBytes op bytes} : r.leb prefixBytes (r.index subopcode) →
      r.simd subopcode op bytes → ImmediateWith r (r.byte 0xfd) (.plain op) (prefixBytes ++ bytes)
  | block {bt bytes} : r.block bt bytes → ImmediateWith r (r.byte 0x02) (.block bt) bytes
  | loop {bt bytes} : r.block bt bytes → ImmediateWith r (r.byte 0x03) (.loop bt) bytes
  | if_ {bt bytes} : r.block bt bytes → ImmediateWith r (r.byte 0x04) (.if_ bt) bytes
  | else_ : ImmediateWith r (r.byte 0x05) .else_ []
  | end_ : ImmediateWith r (r.byte 0x0B) .end_ []

abbrev nativeInstructionOperands : InstructionOperands UInt8 Nat blocktype :=
  ⟨id, id, Scalar.Immediate, NumericExtensions.signInstruction, NumericExtensions.saturatingInstruction,
    ReferencesBinary.Immediate, BulkBinary.Immediate, Simd.Immediate, BlockEncoding, Leb128.U32Encoding⟩

abbrev Immediate := ImmediateWith nativeInstructionOperands

def TokenEncodingWith (immediate : β → τ → List β → Prop) (token : τ) (bytes : List β) : Prop :=
  ∃ opcode rest, bytes = opcode :: rest ∧ immediate opcode token rest

abbrev TokenEncoding := TokenEncodingWith Immediate

end WebAssembly.Binary
