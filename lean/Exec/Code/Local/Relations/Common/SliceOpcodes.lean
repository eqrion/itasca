import Exec.Code.Local.Lowering.Common.NumericEncoding
import Exec.Code.Local.Relations.Common.SliceTokens
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code
/-- Opcode bytes implemented by the first complete integer/control slice. -/
def SliceOpcode (opcode : U8) : Prop :=
  opcode.val ∈ [0, 1, 2, 3, 4, 5, 11, 12, 13, 15, 16, 26, 32, 33, 34, 65, 66, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 103, 104, 105, 192, 193, 121, 122, 123, 194, 195, 196, 69, 80, 167, 173, 172]

def SliceBaseOpcode (opcode : U8) : Prop :=
  opcode.val ∈ [0x00,0x01,0x02,0x03,0x04,0x05,0x0B,0x0C,0x0D,0x0F,0x10,
    0x1A,0x20,0x21,0x22,0x41,0x42,0x45,0x46,0x49,0x50,0x51,0x54,
    0x6A,0x6B,0x7C,0x7D]


/-- Decidable outer-instruction check used only to exclude unsupported binary
encodings; structured bodies are checked separately by SliceInstr. -/
def SliceHead : instr → Bool
  | .NOP | .UNREACHABLE | .DROP | .LOCAL_GET _ | .LOCAL_SET _ | .LOCAL_TEE _
  | .BLOCK _ _ | .LOOP _ _ | .IFELSE _ _ _ | .BR _ | .BR_IF _ | .CALL _ | .RETURN => true
  | .CONST _ (.mk_num__0 _ _) => true
  | .BINOP _ (.mk_binop__0 _ _) => true
  | .UNOP _ (.mk_unop__0 _ _) => true
  | .CVTOP _ _ (.mk_cvtop___0 .I64 .I32 .WRAP)
  | .CVTOP _ _ (.mk_cvtop___0 .I32 .I64 (.EXTEND _)) => true
  | .TESTOP _ (.mk_testop__0 _ .EQZ) => true
  | .RELOP _ (.mk_relop__0 _ _) => true
  | _ => false

theorem slice_head {instruction} (supported : Abs.SliceInstr instruction) :
    SliceHead instruction = true := by
  cases supported <;> try rfl
  case numeric op =>
    cases op with
    | binary ty operator => cases ty <;> rfl
    | compare ty operator => cases ty <;> rfl
    | eqz ty => cases ty <;> rfl
    | unary ty operator => cases ty <;> cases operator <;> rfl
    | conversion operator => cases operator <;> rfl

set_option maxHeartbeats 2000000 in
theorem numeric_slice_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (supported : Abs.SliceInstr operation.instruction) : SliceOpcode opcode := by
  have head := slice_head supported
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals first | solve | simp_all [SliceOpcode] | contradiction
theorem memory_not_slice {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (supported : Abs.SliceInstr (operation.op arg)) : False := by
  have head := slice_head supported
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

theorem wasm1_immediate_slice_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) (supported : Wasm1.SliceToken token) :
    SliceOpcode opcode := by
  cases encoded <;> try { simp [SliceOpcode] }
  all_goals change Abs.SliceInstr _ at supported
  all_goals first
    | exact numeric_slice_opcode (by assumption) supported
    | exact False.elim (memory_not_slice _ (by assumption) supported)
    | have head := slice_head supported; contradiction

set_option maxHeartbeats 2000000 in
theorem sign_slice_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (_supported : Abs.SliceInstr operation.instruction) : SliceOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [SliceOpcode]

set_option maxHeartbeats 2000000 in
theorem saturating_not_slice {opcode operation}
    (meaning : Wasm2.NumericExtensions.saturatingMeaning opcode = some operation)
    (supported : Abs.SliceInstr operation.instruction) : False := by
  have head := slice_head supported
  unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

private def simdPureSupported (n : Nat) : Bool :=
  match Wasm2.Simd.pureMeaning n with
  | none => false
  | some operation => SliceHead operation.instruction

private theorem simd_pure_table : ∀ n : Fin 256, simdPureSupported n.val = false := by
  decide

theorem simd_pure_head {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation) :
    SliceHead operation.instruction = false := by
  have checked := simd_pure_table ⟨opcode, Wasm2.Simd.pure_bound meaning⟩
  simpa only [simdPureSupported, meaning] using checked

theorem simd_pure_not_slice {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation)
    (supported : Abs.SliceInstr operation.instruction) : False := by
  have head := slice_head supported
  rw [simd_pure_head meaning] at head
  contradiction

set_option maxHeartbeats 4000000 in
theorem simd_lane_not_slice {opcode operation} (lane : laneidx)
    (meaning : Wasm2.Simd.laneMeaning opcode = some operation)
    (supported : Abs.SliceInstr (operation.instruction lane)) : False := by
  have head := slice_head supported
  unfold Wasm2.Simd.laneMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

set_option maxHeartbeats 4000000 in
theorem simd_memory_not_slice {opcode operation} (arg : memarg) (lane : laneidx)
    (meaning : Wasm2.Simd.memoryMeaning opcode = some operation)
    (supported : Abs.SliceInstr (operation.instruction arg lane)) : False := by
  have head := slice_head supported
  unfold Wasm2.Simd.memoryMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

theorem simd_not_slice {opcode instruction bytes}
    (encoded : Wasm2.Simd.Immediate opcode instruction bytes)
    (supported : Abs.SliceInstr instruction) : False := by
  cases encoded with
  | pure _ _ meaning => exact simd_pure_not_slice meaning supported
  | lane _ _ _ meaning => exact simd_lane_not_slice _ meaning supported
  | memory _ _ _ meaning _ _ _ => exact simd_memory_not_slice _ _ meaning supported
  | memoryLane _ _ _ _ meaning _ _ _ => exact simd_memory_not_slice _ _ meaning supported
  | constant _ _ _ _ | shuffle _ _ _ _ =>
    have head := slice_head supported
    contradiction

theorem wasm2_immediate_slice_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) (supported : Wasm2.SliceToken token) :
    SliceOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [SliceOpcode]
  | plain encoded => exact wasm1_immediate_slice_opcode encoded supported
  | signExtension _ _ meaning => exact sign_slice_opcode meaning supported
  | saturating _ _ meaning _ => exact False.elim (saturating_not_slice meaning supported)
  | reference encoded => cases encoded <;> have head := slice_head supported <;> contradiction
  | bulk _ _ encoded => cases encoded <;> have head := slice_head supported <;> contradiction
  | simd _ _ encoded => exact False.elim (simd_not_slice encoded supported)

theorem SliceOpcode.base_or_numeric {opcode : U8} (supported : SliceOpcode opcode) :
    SliceBaseOpcode opcode ∨ ∃ op : Abs.Numeric.Instruction, UScalar.cast .U8 (integerOpcode op) = opcode := by
  simp only [SliceOpcode, List.mem_cons, List.mem_nil_iff, or_false] at supported
  rcases supported with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have equal : opcode = 0#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 1#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 5#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 11#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 15#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 16#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 26#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 32#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 33#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 34#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 65#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 66#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 106#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 107#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 108#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.MUL), rfl⟩
  · have equal : opcode = 109#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.DIV .S), rfl⟩
  · have equal : opcode = 110#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.DIV .U), rfl⟩
  · have equal : opcode = 111#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.REM .S), rfl⟩
  · have equal : opcode = 112#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.REM .U), rfl⟩
  · have equal : opcode = 113#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.AND), rfl⟩
  · have equal : opcode = 114#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.OR), rfl⟩
  · have equal : opcode = 115#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.XOR), rfl⟩
  · have equal : opcode = 116#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.SHL), rfl⟩
  · have equal : opcode = 117#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.SHR .S), rfl⟩
  · have equal : opcode = 118#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.SHR .U), rfl⟩
  · have equal : opcode = 119#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.ROTL), rfl⟩
  · have equal : opcode = 120#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I32 (.ROTR), rfl⟩
  · have equal : opcode = 124#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 125#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 126#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.MUL), rfl⟩
  · have equal : opcode = 127#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.DIV .S), rfl⟩
  · have equal : opcode = 128#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.DIV .U), rfl⟩
  · have equal : opcode = 129#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.REM .S), rfl⟩
  · have equal : opcode = 130#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.REM .U), rfl⟩
  · have equal : opcode = 131#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.AND), rfl⟩
  · have equal : opcode = 132#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.OR), rfl⟩
  · have equal : opcode = 133#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.XOR), rfl⟩
  · have equal : opcode = 134#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.SHL), rfl⟩
  · have equal : opcode = 135#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.SHR .S), rfl⟩
  · have equal : opcode = 136#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.SHR .U), rfl⟩
  · have equal : opcode = 137#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.ROTL), rfl⟩
  · have equal : opcode = 138#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.binary .I64 (.ROTR), rfl⟩
  · have equal : opcode = 70#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 71#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.NE), rfl⟩
  · have equal : opcode = 72#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.LT .S), rfl⟩
  · have equal : opcode = 73#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 74#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.GT .S), rfl⟩
  · have equal : opcode = 75#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.GT .U), rfl⟩
  · have equal : opcode = 76#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.LE .S), rfl⟩
  · have equal : opcode = 77#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.LE .U), rfl⟩
  · have equal : opcode = 78#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.GE .S), rfl⟩
  · have equal : opcode = 79#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I32 (.GE .U), rfl⟩
  · have equal : opcode = 81#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 82#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.NE), rfl⟩
  · have equal : opcode = 83#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.LT .S), rfl⟩
  · have equal : opcode = 84#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 85#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.GT .S), rfl⟩
  · have equal : opcode = 86#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.GT .U), rfl⟩
  · have equal : opcode = 87#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.LE .S), rfl⟩
  · have equal : opcode = 88#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.LE .U), rfl⟩
  · have equal : opcode = 89#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.GE .S), rfl⟩
  · have equal : opcode = 90#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.compare .I64 (.GE .U), rfl⟩
  · have equal : opcode = 103#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I32 .clz, rfl⟩
  · have equal : opcode = 104#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I32 .ctz, rfl⟩
  · have equal : opcode = 105#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I32 .popcnt, rfl⟩
  · have equal : opcode = 192#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I32 .extend8, rfl⟩
  · have equal : opcode = 193#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I32 .extend16, rfl⟩
  · have equal : opcode = 121#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .clz, rfl⟩
  · have equal : opcode = 122#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .ctz, rfl⟩
  · have equal : opcode = 123#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .popcnt, rfl⟩
  · have equal : opcode = 194#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .extend8, rfl⟩
  · have equal : opcode = 195#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .extend16, rfl⟩
  · have equal : opcode = 196#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.unary .I64 .extend32, rfl⟩
  · have equal : opcode = 69#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 80#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inl (by unfold SliceBaseOpcode; decide)
  · have equal : opcode = 167#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.conversion .wrap, rfl⟩
  · have equal : opcode = 173#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.conversion .extendUnsigned, rfl⟩
  · have equal : opcode = 172#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact Or.inr ⟨.conversion .extendSigned, rfl⟩

end Exec.Code

namespace Itasca.Wasm1
/-- The actual next byte of a supported token selects one of the proved
integer/control reader cases. -/
theorem At.slice_opcode {data start token next}
    (encoded : At data start token next) (supported : SliceToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.SliceOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm1_immediate_slice_opcode grammar supported

/-- Source-slice membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_slice_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.SliceInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.SliceOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_slice_token supported before remaining
  exact atToken.slice_opcode allowed remaining
end Itasca.Wasm1

namespace Itasca.Wasm2
/-- The actual next byte of a supported token selects one of the proved
integer/control reader cases. -/
theorem At.slice_opcode {data start token next}
    (encoded : At data start token next) (supported : SliceToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.SliceOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_slice_opcode grammar supported

/-- Source-slice membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_slice_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.SliceInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.SliceOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_slice_token supported before remaining
  exact atToken.slice_opcode allowed remaining
end Itasca.Wasm2
