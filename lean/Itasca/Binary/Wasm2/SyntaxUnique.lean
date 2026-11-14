import Itasca.Binary.Wasm2.DeclaredReferences
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Binary.SignedLeb32
import Itasca.Binary.UnicodeUnique
import Itasca.Binary.Wasm2.Syntax
import Itasca.Binary.Wasm2.BlockType

/-!
Sections, each formerly its own module: Simd, Encoding, SyntaxComplete, EncodingComplete, SimdBitsMeaning, SyntaxUnique.
-/

/-! ## Simd -/

section

/-!
# Wasm 2.0 SIMD instruction bytes

`Simd.Immediate` relates a `0xfd` subopcode to its SpecTec instruction and immediate bytes. It
covers pure, lane, memory and lane-memory instructions through the tables in
`Binary/Wasm2/SimdPureMeaning`, `Binary/Wasm2/SimdLaneMeaning` and
`Binary/Wasm2/SimdMemoryMeaning`, and the `v128.const` and `i8x16.shuffle` forms.
`Immediate.wellFormed` shows each is well formed, and `Immediate.prefix_unique` shows that the
bytes determine the instruction.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- A `v128.const` of 128 immediate bits, given as two little-endian 64-bit halves. -/
def vectorConstant (low high : U64) : instr :=
  .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))

/-- The first `count` little-endian bytes of a natural number. -/
def unpackBytes (bits : Nat) (count : Nat) : List Nat :=
  match count with
  | 0 => []
  | n + 1 => bits % 256 :: unpackBytes (bits / 256) n

/-- The sixteen lane indices of an `i8x16.shuffle`, from the bytes of its two 64-bit halves. -/
def shuffleIndices (low high : U64) : List laneidx :=
  ((unpackBytes low.val 8) ++ (unpackBytes high.val 8)).map uN.mk_uN

/-- An `i8x16.shuffle` with the lane indices of the two halves. -/
def shuffle (low high : U64) : instr :=
  .VSHUFFLE (.mk_ishape (.X .I8 (.mk_dim 16))) (shuffleIndices low high)

/-- `unpackBytes` returns `count` bytes. -/
theorem unpackBytes_length (bits count : Nat) : (unpackBytes bits count).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ n ih => simp [unpackBytes, ih]

/-- Unpacked bytes are below 256. -/
theorem unpackBytes_lt (bits count : Nat) : ∀ b ∈ unpackBytes bits count, b < 256 := by
  induction count generalizing bits with
  | zero => simp [unpackBytes]
  | succ n ih =>
    intro b hb
    simp only [unpackBytes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ hb

/-- A vector constant is well formed. -/
theorem vectorConstant_wf (low high : U64) : wf_instr (vectorConstant low high) := by
  apply wf_instr.instr_case_20
  · decide
  · constructor
    have hlo : low.val ≤ 18446744073709551615 := by scalar_tac
    have hhi : high.val ≤ 18446744073709551615 := by scalar_tac
    norm_num [size, valtype_vectype]
    omega

/-- A shuffle is well formed. -/
theorem shuffle_wf (low high : U64) : wf_instr (shuffle low high) := by
  apply wf_instr.instr_case_32
  · apply wf_ishape.ishape_case_0 .I8
    · repeat' first | decide | constructor
    · rfl
  · intro lane hl
    simp only [shuffleIndices, List.mem_map, List.mem_append] at hl
    obtain ⟨n, hn, rfl⟩ := hl
    constructor
    rcases hn with hn | hn
    · have := unpackBytes_lt _ _ _ hn
      norm_num
      omega
    · have := unpackBytes_lt _ _ _ hn
      norm_num
      omega
  · exact ⟨rfl, by simp [shuffleIndices, unpackBytes_length]⟩

/-- The immediate bytes that follow a SIMD subopcode, including all valid `u32` LEB128 encodings of
memory arguments. The prefix and subopcode bytes belong to the enclosing grammar. -/
inductive Immediate : U32 → instr → List U8 → Prop where
  | pure (opcode : U32) (op : Operation) : pureMeaning opcode.val = some op →
      Immediate opcode op.instruction []
  | lane (opcode : U32) (op : LaneOperation) (lane : U8) :
      laneMeaning opcode.val = some op →
      Immediate opcode (op.instruction (.mk_uN lane.val)) [lane]
  | memory (opcode : U32) (op : MemoryOperation) (arg : code.MemArg) {align offset} :
      memoryMeaning opcode.val = some op → op.laneCount = 0 →
      Leb128.Encoding align arg.align.val → Leb128.Encoding offset arg.offset.val →
      Immediate opcode (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)) (align ++ offset)
  | memoryLane (opcode : U32) (op : MemoryOperation) (arg : code.MemArg) (lane : U8)
      {align offset} : memoryMeaning opcode.val = some op → op.laneCount ≠ 0 →
      Leb128.Encoding align arg.align.val → Leb128.Encoding offset arg.offset.val →
      Immediate opcode (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
        (align ++ offset ++ [lane])
  | constant (low high : U64) {lower upper} :
      FloatBits.Encoding 8 lower low.val → FloatBits.Encoding 8 upper high.val →
      Immediate 12#u32 (vectorConstant low high) (lower ++ upper)
  | shuffle (low high : U64) {lower upper} :
      FloatBits.Encoding 8 lower low.val → FloatBits.Encoding 8 upper high.val →
      Immediate 13#u32 (Simd.shuffle low high) (lower ++ upper)

end Itasca.Wasm2.Simd

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

open ModuleBinary

private theorem pure_lane_disjoint {n op lane} (hp : pureMeaning n = some op)
    (hl : laneMeaning n = some lane) : False := by
  rw [lane_pure_none hl] at hp
  contradiction

private theorem pure_memory_disjoint {n op mem} (hp : pureMeaning n = some op)
    (hm : memoryMeaning n = some mem) : False := by
  rw [memory_pure_none hm] at hp
  contradiction

private theorem lane_memory_disjoint {n lane mem} (hl : laneMeaning n = some lane)
    (hm : memoryMeaning n = some mem) : False := by
  rw [memory_lane_none hm] at hl
  contradiction

/-- SIMD immediates are prefix-unique. -/
theorem Immediate.prefix_unique (subopcode : U32) : PrefixUnique (Immediate subopcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact False.elim (pure_lane_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (pure_memory_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (lane_memory_disjoint ‹_› ‹_›) }
  case pure.pure =>
    rename_i op hp op' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact ⟨rfl, rfl, heq⟩
  case lane.lane =>
    rename_i op lane hp op' lane' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i op arg align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, rfl⟩ := leb_prefix_unique ho ho' hrest
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have he : arg = arg' := by cases arg; cases arg'; simp_all
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case memory.memoryLane =>
    rename_i op arg align offset hc ha ho hp op' arg' lane align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc' hc)
  case memoryLane.memory =>
    rename_i op arg lane align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc hc')
  case memoryLane.memoryLane =>
    rename_i op arg lane align offset hc ha ho hp op' arg' lane' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, htail⟩ := leb_prefix_unique ho ho' (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl⟩ := List.cons.inj htail
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have he : arg = arg' := by cases arg; cases arg'; simp_all
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case constant.constant | shuffle.shuffle =>
    rename_i low high lower upper hlo hhi low' high' lower' upper' hlo' hhi'
    obtain ⟨hloeq, rfl, hrest⟩ := float_prefix_unique 8 hlo hlo' (by simpa [List.append_assoc] using heq)
    obtain ⟨hhieq, rfl, rfl⟩ := float_prefix_unique 8 hhi hhi' hrest
    obtain rfl := UScalar.eq_of_val_eq hloeq
    obtain rfl := UScalar.eq_of_val_eq hhieq
    exact ⟨rfl, rfl, rfl⟩

end Itasca.Wasm2.Simd

end

/-! ## Encoding -/

section

/-!
# Wasm 2.0 instruction binary grammar

The handwritten binary grammar of Wasm 2.0 instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, reusing the Wasm 1.0 plain instructions and adding sign extension,
saturating truncation, reference, bulk memory, SIMD and structured control with `BlockEncoding`
block types. `At`, `Consumed` and `BodyEncoding` place tokens, token runs and complete bodies in a
byte slice, as in `Binary/Wasm1/Encoding`. The grammar does not mention validation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A block type as a literal tag byte or a nonnegative signed 33-bit type index. -/
def BlockEncoding (bt : signature.BlockType) (bytes : List U8) : Prop :=
  match bt with
  | .Empty => bytes = [64#u8]
  | .Value t => bytes = [valueByte t]
  | .TypeIndex i => SignedLeb33.Encoding bytes i.val

/-- `BlockDecoded` at a cursor is a `BlockEncoding` over an interval of the input. -/
theorem blockDecoded_iff {data pos bt next} :
    BlockDecoded data pos bt next ↔
      ∃ bytes, BlockEncoding bt bytes ∧ Wasm1.BytesAt data pos bytes next := by
  cases bt with
  | Empty | Value _ =>
    constructor
    · rintro ⟨hp, hv, hn⟩
      exact ⟨_, rfl, .byte data pos next _ hp hv hn⟩
    · rintro ⟨bytes, rfl, hs⟩
      have hn : next.val = pos.val + 1 := by simpa using hs.length
      have hp : pos.val < data.length := by have := hs.bound; omega
      refine ⟨hp, ?_, hn⟩
      have hh := congrArg List.head? hs.suffix
      simpa only [List.drop_eq_getElem_cons hp, List.singleton_append,
        List.head?_cons, Option.some.injEq] using hh
  | TypeIndex i =>
    exact ⟨fun ⟨bs, hs, hl, hb, he⟩ => ⟨bs, he, hs, hl, hb⟩,
      fun ⟨bs, he, hs, hl, hb⟩ => ⟨bs, hs, hl, hb, he⟩⟩

/-- The immediate bytes that follow an opcode byte for a Wasm 2.0 token. Plain Wasm 1.0 leaves are
reused, but structured instructions take `BlockEncoding` block types. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | plain {opcode op bytes} : Wasm1.Immediate opcode (.plain op) bytes →
      Immediate opcode (.plain op) bytes
  | signExtension (opcode : U8) (operation : Numeric.Operation) :
      NumericExtensions.signMeaning opcode = some operation →
      Immediate opcode (.plain operation.instruction) []
  | saturating (subopcode : U32) (operation : Numeric.Operation) {bytes} :
      NumericExtensions.saturatingMeaning subopcode = some operation →
      Leb128.Encoding bytes subopcode.val → Immediate 0xFC#u8 (.plain operation.instruction) bytes
  | reference {opcode op bytes} : ReferencesBinary.Immediate opcode op bytes →
      Immediate opcode (.plain op) bytes
  | bulk (subopcode : U32) {prefixBytes op bytes} : Leb128.Encoding prefixBytes subopcode.val →
      BulkBinary.Immediate subopcode op bytes → Immediate 0xfc#u8 (.plain op) (prefixBytes ++ bytes)
  | simd (subopcode : U32) {prefixBytes op bytes} : Leb128.Encoding prefixBytes subopcode.val →
      Simd.Immediate subopcode op bytes → Immediate 0xfd#u8 (.plain op) (prefixBytes ++ bytes)
  | block {bt bytes} : BlockEncoding bt bytes → Immediate 0x02#u8 (.block bt) bytes
  | loop {bt bytes} : BlockEncoding bt bytes → Immediate 0x03#u8 (.loop bt) bytes
  | if_ {bt bytes} : BlockEncoding bt bytes → Immediate 0x04#u8 (.if_ bt) bytes
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []

/-- A token as its opcode byte followed by its immediate bytes. -/
def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

/-- A token is encoded by the interval from `start` to `next`. The suffix is unrestricted. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ Wasm1.BytesAt data start bytes next

/-- The tokens read from `start` to the cursor, accumulated one `At` step at a time. Unread bytes
are unconstrained. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- A complete function body: the tokens read from offset 0 reach the end of `data`, and end with
the final `end`. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧
    next.val = data.length ∧ BodyTokens tokens ops

/-- A token interval is nonempty and within the input. -/
theorem At.span {data start token next} (h : At data start token next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨_, ⟨op, imm, rfl, _⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons] at this
  exact ⟨by omega, hs.bound⟩

/-- Composes an opcode byte with an immediate byte span. -/
theorem At.of_immediate {data start pos next opcode token immediate}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himmediate : Immediate opcode token immediate)
    (hspan : Wasm1.BytesAt data pos immediate next) : At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (Wasm1.BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

/-- A structured instruction header token from a decoded block type. -/
theorem At.of_block_type {data start pos next opcode token} (bt : signature.BlockType)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, BlockEncoding bt bytes → Immediate opcode token bytes)
    (hdecoded : BlockDecoded data pos bt next) : At data start token next := by
  obtain ⟨bytes, he, hs⟩ := blockDecoded_iff.mp hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) hs

/-- A Wasm 1.0 plain token is a Wasm 2.0 token. -/
theorem At.plain {data start op next} (h : Wasm1.At data start (.plain op) next) :
    At data start (.plain op) next := by
  obtain ⟨bs, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  exact ⟨_, ⟨opcode, imm, rfl, .plain hi⟩, hs⟩

/-- A consumed span is within the input. -/
theorem Consumed.span {data start tokens next} (h : Consumed data start tokens next) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil hb => exact ⟨Nat.le_refl _, hb⟩
  | snoc _ ha ih => have := ha.span; omega

/-- Consumed spans compose. -/
theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

end Itasca.Wasm2

end

/-! ## SyntaxComplete -/

section

/-!
# Instruction-by-instruction view of Wasm 2.0 syntax

`Atom` gives the complete token spelling of one instruction, and `Spells` is the left-to-right
form of `Emits`. `Emits.cons_iff` splits the next instruction and its tokens, including nested
delimiters, off the remaining syntax.
-/

namespace Itasca.Wasm2

/-- The complete flat token spelling of a single instruction, including nested delimiters. -/
inductive Atom : List Token → instr → Prop where
  | simple {token op} : Simple token op → Atom [token] op
  | block {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.block bt] ++ tokens ++ [.end_]) (.BLOCK (blockType bt) ops)
  | loop {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.loop bt] ++ tokens ++ [.end_]) (.LOOP (blockType bt) ops)
  | ifElse {yesTokens yes noTokens no} (bt : signature.BlockType) :
      Emits yesTokens yes → Emits noTokens no →
      Atom ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
        (.IFELSE (blockType bt) yes no)
  | ifEnd {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.if_ bt] ++ tokens ++ [.end_]) (.IFELSE (blockType bt) ops [])

/-- An atom emits its instruction. -/
theorem Atom.emits {tokens op} (h : Atom tokens op) : Emits tokens [op] := by
  cases h with
  | simple hs => simpa using Emits.simple .nil hs
  | block bt hb => simpa using Emits.block bt .nil hb
  | loop bt hb => simpa using Emits.loop bt .nil hb
  | ifElse bt hy hn => simpa using Emits.ifElse bt .nil hy hn
  | ifEnd bt hb => simpa using Emits.ifEnd bt .nil hb

theorem Atom.nonempty {tokens op} (h : Atom tokens op) : tokens ≠ [] := by
  cases h <;> simp

/-- A left-to-right presentation of `Emits` as a concatenation of atoms. -/
inductive Spells : List Token → List instr → Prop where
  | nil : Spells [] []
  | cons {first rest op ops} : Atom first op → Spells rest ops →
      Spells (first ++ rest) (op :: ops)

theorem Spells.append {xs ys ops rest} (hx : Spells xs ops) (hy : Spells ys rest) :
    Spells (xs ++ ys) (ops ++ rest) := by
  induction hx with
  | nil => exact hy
  | cons h _ ih => simpa [List.append_assoc] using Spells.cons h ih

/-- `Spells` implies `Emits`. -/
theorem Spells.emits {tokens ops} (h : Spells tokens ops) : Emits tokens ops := by
  induction h with
  | nil => exact .nil
  | cons hop _ ih => simpa using hop.emits.append ih

/-- `Emits` implies `Spells`. -/
theorem Emits.spells {tokens ops} (h : Emits tokens ops) : Spells tokens ops := by
  induction h with
  | nil => exact .nil
  | simple _ hs ih =>
    simpa using ih.append (.cons (.simple hs) .nil)
  | block bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.block bt hb) .nil)
  | loop bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.loop bt hb) .nil)
  | ifElse bt _ hy hn ih _ _ =>
    simpa [List.append_assoc] using ih.append (.cons (.ifElse bt hy hn) .nil)
  | ifEnd bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.ifEnd bt hb) .nil)

theorem Emits.empty_iff {tokens} : Emits tokens [] ↔ tokens = [] := by
  constructor
  · intro h
    have hs := h.spells
    cases hs
    rfl
  · rintro rfl
    exact .nil

/-- Splits the first instruction and its tokens, including all nested delimiters, off the rest of
the syntax. -/
theorem Emits.cons_iff {tokens op ops} :
    Emits tokens (op :: ops) ↔
      ∃ first rest, tokens = first ++ rest ∧ Atom first op ∧ Emits rest ops := by
  constructor
  · intro h
    have hs := h.spells
    cases hs with
    | cons hop ht => exact ⟨_, _, rfl, hop, ht.emits⟩
  · rintro ⟨first, rest, rfl, hop, ht⟩
    simpa using hop.emits.append ht

end Itasca.Wasm2

end

/-! ## EncodingComplete -/

section

/-!
# Reading Wasm 2.0 encodings

Splitting lemmas for the Wasm 2.0 `At` and `Consumed` relations, as in
`Binary/Wasm1/EncodingComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A token interval is its opcode byte at the cursor followed by an immediate span. -/
theorem At.immediate {data start token next} (h : At data start token next)
    (pos : Usize) (hpos : pos.val = start.val + 1) :
    ∃ opcode immediate, Immediate opcode token immediate ∧
      (∃ hp : start.val < data.length, data.val[start.val] = opcode) ∧
      Wasm1.BytesAt data pos immediate next := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  have hl := hs.length
  have hb := hs.bound
  simp only [List.length_cons] at hl
  have hp : start.val < data.length := by omega
  have heq := hs.suffix
  rw [List.drop_eq_getElem_cons hp] at heq
  refine ⟨opcode, imm, hi, ⟨hp, (List.cons.inj heq).1⟩, ?_⟩
  exact ⟨by simpa [hpos] using (List.cons.inj heq).2, by omega, hb⟩

/-- A consumed span splits at any token boundary. -/
theorem Consumed.split_eq {data start tokens next} (h : Consumed data start tokens next)
    (first rest : List Token) (heq : tokens = first ++ rest) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next := by
  induction h generalizing first rest with
  | nil hb =>
      have hempty : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases hempty with ⟨rfl, rfl⟩
      exact ⟨start, .nil start hb, .nil start hb⟩
  | @snoc tokens pos token next hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = tokens ++ [token] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil next hlast.span.2⟩
      | append_singleton rest last =>
          have heq' : tokens ++ [token] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : token = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          have hp : tokens = first ++ rest := List.append_cancel_right heq'
          obtain ⟨middle, hf, hr⟩ := ih first rest hp
          exact ⟨middle, hf, .snoc hr hlast⟩

/-- A consumed span of a concatenation splits into consecutive spans. -/
theorem Consumed.split {data start next first rest}
    (h : Consumed data start (first ++ rest) next) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next :=
  h.split_eq first rest rfl

/-- An empty token list leaves the cursor in place. -/
theorem Consumed.empty_eq {data start tokens next}
    (h : Consumed data start tokens next) (he : tokens = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

/-- A consumed span of one token is an `At`. -/
theorem Consumed.single {data start next token}
    (h : Consumed data start [token] next) : At data start token next := by
  generalize he : [token] = tokens at h
  cases h with
  | nil => simp at he
  | @snoc tokens pos last next hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : tokens = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = token := by simpa [ht] using he.symm
      have hpos := hp.empty_eq ht
      simpa [heq, hpos] using hl

/-- A nonempty consumed span is its first token followed by the rest. -/
theorem Consumed.cons_iff {data start next token tokens} :
    Consumed data start (token :: tokens) next ↔
      ∃ middle, At data start token middle ∧ Consumed data middle tokens next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := h.split_eq [token] tokens rfl
    exact ⟨middle, hh.single, ht⟩
  · rintro ⟨middle, hh, ht⟩
    have hb : start.val ≤ data.length := by have := hh.span; omega
    exact Consumed.append (.snoc (.nil start hb) hh) ht

end Itasca.Wasm2

end

/-! ## SimdBitsMeaning -/

section

/-!
# Typing and declared references of SIMD constants

Shows that `v128.const` and `i8x16.shuffle` have the expected `Instr_ok` typing
(`vectorConstant_typed`, `shuffle_typed`), that a generated typing fixes their stack effect
(`vectorConstant_principal`, `shuffle_principal`, `shuffle_bound`), and that they carry no
`ref.func`. `shuffleIndices_encoding` relates the lane indices to the immediate bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- A vector constant has type `[] -> [v128]`. -/
theorem vectorConstant_typed (C : context) (low high : U64) (hC : wf_context C) :
    Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list []) (.mk_list [.V128])) :=
  .vconst C _ hC (vectorConstant_wf low high)

/-- A generated typing of a vector constant has the stack effect `[] -> [v128]`. -/
theorem vectorConstant_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

/-- Unpacking the value of a byte list recovers the bytes. -/
theorem unpackBytes_payload (bytes : List U8) :
    unpackBytes (FloatBits.payload bytes) bytes.length = bytes.map UScalar.val := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [FloatBits.payload, List.length_cons, unpackBytes, List.map_cons]
    have hm : (b.val + 256 * FloatBits.payload bs) % 256 = b.val := by omega
    have hd : (b.val + 256 * FloatBits.payload bs) / 256 = FloatBits.payload bs := by omega
    rw [hm, hd, ih]

/-- The lane indices of a shuffle are the bytes of its two immediate halves. -/
theorem shuffleIndices_encoding (low high : U64) (lower upper : List U8)
    (hl : FloatBits.Encoding 8 lower low.val) (hh : FloatBits.Encoding 8 upper high.val) :
    shuffleIndices low high = (lower ++ upper).map (fun b => uN.mk_uN b.val) := by
  have hlo : unpackBytes low.val 8 = lower.map UScalar.val := by
    rw [hl.2, ← hl.1, unpackBytes_payload]
  have hhi : unpackBytes high.val 8 = upper.map UScalar.val := by
    rw [hh.2, ← hh.1, unpackBytes_payload]
  simp [shuffleIndices, hlo, hhi, List.map_append, List.map_map, Function.comp_def]

/-- A shuffle with lane indices below 32 has type `[v128, v128] -> [v128]`. -/
theorem shuffle_typed (C : context) (low high : U64) (hC : wf_context C)
    (hl : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) :
    Instr_ok C (shuffle low high)
      (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128])) := by
  exact .vshuffle C _ _ (.mk_dim 16) (by constructor; constructor; decide)
    hl hC (by constructor; decide) (shuffle_wf low high)

/-- A generated typing of a shuffle has the stack effect `[v128, v128] -> [v128]`. -/
theorem shuffle_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.V128, .V128] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

/-- A generated typing of a shuffle bounds every lane index by 32. -/
theorem shuffle_bound (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
  cases ht
  cases_type fun_dim
  assumption

/-- A vector constant has no declared-reference obligation. -/
theorem vectorConstant_declared (refs : List funcidx) (low high : U64) :
    DeclaredReferences.Instruction refs (vectorConstant low high) := by
  simp [vectorConstant, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

/-- A shuffle has no declared-reference obligation. -/
theorem shuffle_declared (refs : List funcidx) (low high : U64) :
    DeclaredReferences.Instruction refs (shuffle low high) := by
  simp [shuffle, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Wasm2.Simd

end

/-! ## SyntaxUnique -/

section

/-!
# Uniqueness of Wasm 2.0 instruction syntax

`Emits.unique` and `BodyTokens.unique` show that a token list spells at most one instruction
list. The proof folds the tokens with a stack of open structured instructions
(`SyntaxDecode.run`).
-/

namespace Itasca.Wasm2

namespace SyntaxDecode

/-- An open structured instruction awaiting its `end`, with the instructions emitted before it. -/
inductive Frame where
  | block (bt : signature.BlockType) (prior : List instr)
  | loop (bt : signature.BlockType) (prior : List instr)
  | then_ (bt : signature.BlockType) (prior : List instr)
  | else_ (bt : signature.BlockType) (prior yes : List instr)

/-- The instructions emitted at the current nesting level and the stack of open frames. -/
structure State where
  ops : List instr
  parents : List Frame

/-- Processes one token, failing on an `else` or `end` with no matching open frame. -/
def step (s : State) : Token → Option State
  | .plain op => some { s with ops := s.ops ++ [op] }
  | .block bt => some ⟨[], .block bt s.ops :: s.parents⟩
  | .loop bt => some ⟨[], .loop bt s.ops :: s.parents⟩
  | .if_ bt => some ⟨[], .then_ bt s.ops :: s.parents⟩
  | .else_ => match s.parents with
    | .then_ bt prior :: parents => some ⟨[], .else_ bt prior s.ops :: parents⟩
    | _ => none
  | .end_ => match s.parents with
    | .block bt prior :: parents =>
        some ⟨prior ++ [.BLOCK (blockType bt) s.ops], parents⟩
    | .loop bt prior :: parents =>
        some ⟨prior ++ [.LOOP (blockType bt) s.ops], parents⟩
    | .then_ bt prior :: parents =>
        some ⟨prior ++ [.IFELSE (blockType bt) s.ops []], parents⟩
    | .else_ bt prior yes :: parents =>
        some ⟨prior ++ [.IFELSE (blockType bt) yes s.ops], parents⟩
    | [] => none

/-- Processes a token list from a state. -/
def run : List Token → State → Option State
  | [], s => some s
  | t :: ts, s => (step s t).bind (run ts)

theorem run_append (xs ys : List Token) (s : State) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, run]
    cases step s x <;> simp_all

end SyntaxDecode

/-- `SyntaxDecode.run` on an emitting token list appends the emitted instructions. -/
theorem Emits.decode {tokens ops} (h : Emits tokens ops) (s : SyntaxDecode.State) :
    SyntaxDecode.run tokens s = some { s with ops := s.ops ++ ops } := by
  induction h generalizing s with
  | nil => simp [SyntaxDecode.run]
  | simple _ hs ih =>
    cases hs
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, List.append_assoc]
  | block bt _ _ ih ihb | loop bt _ _ ih ihb | ifEnd bt _ _ ih ihb =>
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, ihb, List.append_assoc]
  | ifElse bt _ _ _ ih ihy ihn =>
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, ihy, ihn, List.append_assoc]

/-- A token list determines the structured instructions it spells. -/
theorem Emits.unique {tokens xs ys} (hx : Emits tokens xs) (hy : Emits tokens ys) : xs = ys := by
  have h := (hx.decode ⟨[], []⟩).symm.trans (hy.decode ⟨[], []⟩)
  simpa using congrArg (fun s => s.map SyntaxDecode.State.ops) h

/-- A body's tokens determine its instructions. -/
theorem BodyTokens.unique {tokens xs ys}
    (hx : BodyTokens tokens xs) (hy : BodyTokens tokens ys) : xs = ys := by
  obtain ⟨left, hl, hx⟩ := hx
  obtain ⟨right, hr, hy⟩ := hy
  have he : left = right := List.append_cancel_right (hl.symm.trans hr)
  subst right
  exact hx.unique hy

end Itasca.Wasm2

end
