import Itasca.Binary.Wasm2.SimdMemoryMeaning
import Itasca.Binary.Wasm1.MemoryMeaning
import Itasca.Binary.FloatBits
import Itasca.Binary.PrefixUnique

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
