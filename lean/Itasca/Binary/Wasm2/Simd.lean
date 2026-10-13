import Itasca.Binary.Wasm2.SimdMemoryMeaning
import Itasca.Binary.Wasm1.MemoryMeaning
import Itasca.Binary.FloatBits

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Vector constants retain all 128 immediate bits in little-endian order. -/
def vectorConstant (low high : U64) : instr :=
  .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))

def unpackBytes (bits : Nat) (count : Nat) : List Nat :=
  match count with
  | 0 => []
  | n + 1 => bits % 256 :: unpackBytes (bits / 256) n

/-- Shuffle callback words denote sixteen byte-sized lane indices, in byte order. -/
def shuffleIndices (low high : U64) : List laneidx :=
  ((unpackBytes low.val 8) ++ (unpackBytes high.val 8)).map uN.mk_uN

def shuffle (low high : U64) : instr :=
  .VSHUFFLE (.mk_ishape (.X .I8 (.mk_dim 16))) (shuffleIndices low high)

theorem unpackBytes_length (bits count : Nat) : (unpackBytes bits count).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ n ih => simp [unpackBytes, ih]

theorem unpackBytes_lt (bits count : Nat) : ∀ b ∈ unpackBytes bits count, b < 256 := by
  induction count generalizing bits with
  | zero => simp [unpackBytes]
  | succ n ih =>
    intro b hb
    simp only [unpackBytes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ hb

theorem vectorConstant_wf (low high : U64) : wf_instr (vectorConstant low high) := by
  apply wf_instr.instr_case_20
  · decide
  · constructor
    have hlo : low.val ≤ 18446744073709551615 := by scalar_tac
    have hhi : high.val ≤ 18446744073709551615 := by scalar_tac
    norm_num [size, valtype_vectype]
    omega

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

/-- Independent SIMD immediates, including all valid u32 LEB encodings of
memory arguments. The outer profile grammar supplies the prefix subopcode. -/
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

private theorem memoryArg_wf (arg : code.MemArg) : wf_memarg (MemoryMeaning.memArg arg) := by
  constructor <;> constructor <;> scalar_tac

theorem Immediate.wellFormed {opcode instruction bytes} (h : Immediate opcode instruction bytes) :
    wf_instr instruction := by
  cases h with
  | pure _ op _ => exact op.wellFormed
  | lane _ op lane _ => exact op.wellFormed _ (by constructor; scalar_tac)
  | memory _ op arg _ _ _ _ => exact op.wellFormed _ _ (memoryArg_wf arg) (by constructor; decide)
  | memoryLane _ op arg lane _ _ _ _ =>
      exact op.wellFormed _ _ (memoryArg_wf arg) (by constructor; scalar_tac)
  | constant low high _ _ => exact vectorConstant_wf low high
  | shuffle low high _ _ => exact shuffle_wf low high

end Itasca.Wasm2.Simd
