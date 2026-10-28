import Itasca.Runtime.Code.Local.Callbacks.Simd.CompilerSimdMetadata
import Mathlib.Tactic.IntervalCases

/-! Finite constructor/decoder correspondence. Sixteen bounded chunks keep
elaboration local; each supported opcode still names its expected constructor,
and unsupported cases remain explicit. No shared generated source table is used. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Check the explicitly named expected constructor, then check its decoder.
This expands to ordinary kernel-checked tactics; the opcode table stays explicit. -/
local macro "simd_constructor_case " made:ident instruction:ident expected:term : tactic =>
  `(tactic| (
    change Result.ok (some $expected) = Result.ok (some $instruction) at $made:ident
    have same : $expected = $instruction := by
      simpa only [Result.ok.injEq,Option.some.injEq] using $made
    subst $instruction:ident
    with_unfolding_all rfl))

private theorem make_simd_roundtrip_0 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 0 ≤ op.val) (upper : op.val < 16)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 0 ≤ n at lower
  change n < 16 at upper
  interval_cases n
  · simd_constructor_case made instruction (.V128Load dst a entry)
  · simd_constructor_case made instruction (.V128Load8x8S dst a entry)
  · simd_constructor_case made instruction (.V128Load8x8U dst a entry)
  · simd_constructor_case made instruction (.V128Load16x4S dst a entry)
  · simd_constructor_case made instruction (.V128Load16x4U dst a entry)
  · simd_constructor_case made instruction (.V128Load32x2S dst a entry)
  · simd_constructor_case made instruction (.V128Load32x2U dst a entry)
  · simd_constructor_case made instruction (.V128Load8Splat dst a entry)
  · simd_constructor_case made instruction (.V128Load16Splat dst a entry)
  · simd_constructor_case made instruction (.V128Load32Splat dst a entry)
  · simd_constructor_case made instruction (.V128Load64Splat dst a entry)
  · simd_constructor_case made instruction (.V128Store dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I8x16Shuffle dst a entry)
  · simd_constructor_case made instruction (.I8x16Swizzle dst a entry)
  · simd_constructor_case made instruction (.I8x16Splat dst a entry)

private theorem make_simd_roundtrip_16 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 16 ≤ op.val) (upper : op.val < 32)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 16 ≤ n at lower
  change n < 32 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I16x8Splat dst a entry)
  · simd_constructor_case made instruction (.I32x4Splat dst a entry)
  · simd_constructor_case made instruction (.I64x2Splat dst a entry)
  · simd_constructor_case made instruction (.F32x4Splat dst a entry)
  · simd_constructor_case made instruction (.F64x2Splat dst a entry)
  · simd_constructor_case made instruction (.I8x16ExtractLaneS dst a entry)
  · simd_constructor_case made instruction (.I8x16ExtractLaneU dst a entry)
  · simd_constructor_case made instruction (.I8x16ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtractLaneS dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtractLaneU dst a entry)
  · simd_constructor_case made instruction (.I16x8ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtractLane dst a entry)
  · simd_constructor_case made instruction (.I32x4ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtractLane dst a entry)
  · simd_constructor_case made instruction (.I64x2ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.F32x4ExtractLane dst a entry)

private theorem make_simd_roundtrip_32 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 32 ≤ op.val) (upper : op.val < 48)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 32 ≤ n at lower
  change n < 48 at upper
  interval_cases n
  · simd_constructor_case made instruction (.F32x4ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.F64x2ExtractLane dst a entry)
  · simd_constructor_case made instruction (.F64x2ReplaceLane dst a entry)
  · simd_constructor_case made instruction (.I8x16Eq dst a entry)
  · simd_constructor_case made instruction (.I8x16Ne dst a entry)
  · simd_constructor_case made instruction (.I8x16LtS dst a entry)
  · simd_constructor_case made instruction (.I8x16LtU dst a entry)
  · simd_constructor_case made instruction (.I8x16GtS dst a entry)
  · simd_constructor_case made instruction (.I8x16GtU dst a entry)
  · simd_constructor_case made instruction (.I8x16LeS dst a entry)
  · simd_constructor_case made instruction (.I8x16LeU dst a entry)
  · simd_constructor_case made instruction (.I8x16GeS dst a entry)
  · simd_constructor_case made instruction (.I8x16GeU dst a entry)
  · simd_constructor_case made instruction (.I16x8Eq dst a entry)
  · simd_constructor_case made instruction (.I16x8Ne dst a entry)
  · simd_constructor_case made instruction (.I16x8LtS dst a entry)

private theorem make_simd_roundtrip_48 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 48 ≤ op.val) (upper : op.val < 64)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 48 ≤ n at lower
  change n < 64 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I16x8LtU dst a entry)
  · simd_constructor_case made instruction (.I16x8GtS dst a entry)
  · simd_constructor_case made instruction (.I16x8GtU dst a entry)
  · simd_constructor_case made instruction (.I16x8LeS dst a entry)
  · simd_constructor_case made instruction (.I16x8LeU dst a entry)
  · simd_constructor_case made instruction (.I16x8GeS dst a entry)
  · simd_constructor_case made instruction (.I16x8GeU dst a entry)
  · simd_constructor_case made instruction (.I32x4Eq dst a entry)
  · simd_constructor_case made instruction (.I32x4Ne dst a entry)
  · simd_constructor_case made instruction (.I32x4LtS dst a entry)
  · simd_constructor_case made instruction (.I32x4LtU dst a entry)
  · simd_constructor_case made instruction (.I32x4GtS dst a entry)
  · simd_constructor_case made instruction (.I32x4GtU dst a entry)
  · simd_constructor_case made instruction (.I32x4LeS dst a entry)
  · simd_constructor_case made instruction (.I32x4LeU dst a entry)
  · simd_constructor_case made instruction (.I32x4GeS dst a entry)

private theorem make_simd_roundtrip_64 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 64 ≤ op.val) (upper : op.val < 80)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 64 ≤ n at lower
  change n < 80 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I32x4GeU dst a entry)
  · simd_constructor_case made instruction (.F32x4Eq dst a entry)
  · simd_constructor_case made instruction (.F32x4Ne dst a entry)
  · simd_constructor_case made instruction (.F32x4Lt dst a entry)
  · simd_constructor_case made instruction (.F32x4Gt dst a entry)
  · simd_constructor_case made instruction (.F32x4Le dst a entry)
  · simd_constructor_case made instruction (.F32x4Ge dst a entry)
  · simd_constructor_case made instruction (.F64x2Eq dst a entry)
  · simd_constructor_case made instruction (.F64x2Ne dst a entry)
  · simd_constructor_case made instruction (.F64x2Lt dst a entry)
  · simd_constructor_case made instruction (.F64x2Gt dst a entry)
  · simd_constructor_case made instruction (.F64x2Le dst a entry)
  · simd_constructor_case made instruction (.F64x2Ge dst a entry)
  · simd_constructor_case made instruction (.V128Not dst a entry)
  · simd_constructor_case made instruction (.V128And dst a entry)
  · simd_constructor_case made instruction (.V128Andnot dst a entry)

private theorem make_simd_roundtrip_80 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 80 ≤ op.val) (upper : op.val < 96)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 80 ≤ n at lower
  change n < 96 at upper
  interval_cases n
  · simd_constructor_case made instruction (.V128Or dst a entry)
  · simd_constructor_case made instruction (.V128Xor dst a entry)
  · simd_constructor_case made instruction (.V128Bitselect dst a entry)
  · simd_constructor_case made instruction (.V128AnyTrue dst a entry)
  · simd_constructor_case made instruction (.V128Load8Lane dst a entry)
  · simd_constructor_case made instruction (.V128Load16Lane dst a entry)
  · simd_constructor_case made instruction (.V128Load32Lane dst a entry)
  · simd_constructor_case made instruction (.V128Load64Lane dst a entry)
  · simd_constructor_case made instruction (.V128Store8Lane dst a entry)
  · simd_constructor_case made instruction (.V128Store16Lane dst a entry)
  · simd_constructor_case made instruction (.V128Store32Lane dst a entry)
  · simd_constructor_case made instruction (.V128Store64Lane dst a entry)
  · simd_constructor_case made instruction (.V128Load32Zero dst a entry)
  · simd_constructor_case made instruction (.V128Load64Zero dst a entry)
  · simd_constructor_case made instruction (.F32x4DemoteF64x2Zero dst a entry)
  · simd_constructor_case made instruction (.F64x2PromoteLowF32x4 dst a entry)

private theorem make_simd_roundtrip_96 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 96 ≤ op.val) (upper : op.val < 112)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 96 ≤ n at lower
  change n < 112 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I8x16Abs dst a entry)
  · simd_constructor_case made instruction (.I8x16Neg dst a entry)
  · simd_constructor_case made instruction (.I8x16Popcnt dst a entry)
  · simd_constructor_case made instruction (.I8x16AllTrue dst a entry)
  · simd_constructor_case made instruction (.I8x16Bitmask dst a entry)
  · simd_constructor_case made instruction (.I8x16NarrowI16x8S dst a entry)
  · simd_constructor_case made instruction (.I8x16NarrowI16x8U dst a entry)
  · simd_constructor_case made instruction (.F32x4Ceil dst a entry)
  · simd_constructor_case made instruction (.F32x4Floor dst a entry)
  · simd_constructor_case made instruction (.F32x4Trunc dst a entry)
  · simd_constructor_case made instruction (.F32x4Nearest dst a entry)
  · simd_constructor_case made instruction (.I8x16Shl dst a entry)
  · simd_constructor_case made instruction (.I8x16ShrS dst a entry)
  · simd_constructor_case made instruction (.I8x16ShrU dst a entry)
  · simd_constructor_case made instruction (.I8x16Add dst a entry)
  · simd_constructor_case made instruction (.I8x16AddSatS dst a entry)

private theorem make_simd_roundtrip_112 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 112 ≤ op.val) (upper : op.val < 128)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 112 ≤ n at lower
  change n < 128 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I8x16AddSatU dst a entry)
  · simd_constructor_case made instruction (.I8x16Sub dst a entry)
  · simd_constructor_case made instruction (.I8x16SubSatS dst a entry)
  · simd_constructor_case made instruction (.I8x16SubSatU dst a entry)
  · simd_constructor_case made instruction (.F64x2Ceil dst a entry)
  · simd_constructor_case made instruction (.F64x2Floor dst a entry)
  · simd_constructor_case made instruction (.I8x16MinS dst a entry)
  · simd_constructor_case made instruction (.I8x16MinU dst a entry)
  · simd_constructor_case made instruction (.I8x16MaxS dst a entry)
  · simd_constructor_case made instruction (.I8x16MaxU dst a entry)
  · simd_constructor_case made instruction (.F64x2Trunc dst a entry)
  · simd_constructor_case made instruction (.I8x16AvgrU dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtaddPairwiseI8x16S dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtaddPairwiseI8x16U dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtaddPairwiseI16x8S dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtaddPairwiseI16x8U dst a entry)

private theorem make_simd_roundtrip_128 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 128 ≤ op.val) (upper : op.val < 144)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 128 ≤ n at lower
  change n < 144 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I16x8Abs dst a entry)
  · simd_constructor_case made instruction (.I16x8Neg dst a entry)
  · simd_constructor_case made instruction (.I16x8Q15mulrSatS dst a entry)
  · simd_constructor_case made instruction (.I16x8AllTrue dst a entry)
  · simd_constructor_case made instruction (.I16x8Bitmask dst a entry)
  · simd_constructor_case made instruction (.I16x8NarrowI32x4S dst a entry)
  · simd_constructor_case made instruction (.I16x8NarrowI32x4U dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtendLowI8x16S dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtendHighI8x16S dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtendLowI8x16U dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtendHighI8x16U dst a entry)
  · simd_constructor_case made instruction (.I16x8Shl dst a entry)
  · simd_constructor_case made instruction (.I16x8ShrS dst a entry)
  · simd_constructor_case made instruction (.I16x8ShrU dst a entry)
  · simd_constructor_case made instruction (.I16x8Add dst a entry)
  · simd_constructor_case made instruction (.I16x8AddSatS dst a entry)

private theorem make_simd_roundtrip_144 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 144 ≤ op.val) (upper : op.val < 160)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 144 ≤ n at lower
  change n < 160 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I16x8AddSatU dst a entry)
  · simd_constructor_case made instruction (.I16x8Sub dst a entry)
  · simd_constructor_case made instruction (.I16x8SubSatS dst a entry)
  · simd_constructor_case made instruction (.I16x8SubSatU dst a entry)
  · simd_constructor_case made instruction (.F64x2Nearest dst a entry)
  · simd_constructor_case made instruction (.I16x8Mul dst a entry)
  · simd_constructor_case made instruction (.I16x8MinS dst a entry)
  · simd_constructor_case made instruction (.I16x8MinU dst a entry)
  · simd_constructor_case made instruction (.I16x8MaxS dst a entry)
  · simd_constructor_case made instruction (.I16x8MaxU dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I16x8AvgrU dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtmulLowI8x16S dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtmulHighI8x16S dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtmulLowI8x16U dst a entry)
  · simd_constructor_case made instruction (.I16x8ExtmulHighI8x16U dst a entry)

private theorem make_simd_roundtrip_160 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 160 ≤ op.val) (upper : op.val < 176)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 160 ≤ n at lower
  change n < 176 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I32x4Abs dst a entry)
  · simd_constructor_case made instruction (.I32x4Neg dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I32x4AllTrue dst a entry)
  · simd_constructor_case made instruction (.I32x4Bitmask dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I32x4ExtendLowI16x8S dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtendHighI16x8S dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtendLowI16x8U dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtendHighI16x8U dst a entry)
  · simd_constructor_case made instruction (.I32x4Shl dst a entry)
  · simd_constructor_case made instruction (.I32x4ShrS dst a entry)
  · simd_constructor_case made instruction (.I32x4ShrU dst a entry)
  · simd_constructor_case made instruction (.I32x4Add dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction

private theorem make_simd_roundtrip_176 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 176 ≤ op.val) (upper : op.val < 192)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 176 ≤ n at lower
  change n < 192 at upper
  interval_cases n
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I32x4Sub dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I32x4Mul dst a entry)
  · simd_constructor_case made instruction (.I32x4MinS dst a entry)
  · simd_constructor_case made instruction (.I32x4MinU dst a entry)
  · simd_constructor_case made instruction (.I32x4MaxS dst a entry)
  · simd_constructor_case made instruction (.I32x4MaxU dst a entry)
  · simd_constructor_case made instruction (.I32x4DotI16x8S dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I32x4ExtmulLowI16x8S dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtmulHighI16x8S dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtmulLowI16x8U dst a entry)
  · simd_constructor_case made instruction (.I32x4ExtmulHighI16x8U dst a entry)

private theorem make_simd_roundtrip_192 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 192 ≤ op.val) (upper : op.val < 208)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 192 ≤ n at lower
  change n < 208 at upper
  interval_cases n
  · simd_constructor_case made instruction (.I64x2Abs dst a entry)
  · simd_constructor_case made instruction (.I64x2Neg dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I64x2AllTrue dst a entry)
  · simd_constructor_case made instruction (.I64x2Bitmask dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I64x2ExtendLowI32x4S dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtendHighI32x4S dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtendLowI32x4U dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtendHighI32x4U dst a entry)
  · simd_constructor_case made instruction (.I64x2Shl dst a entry)
  · simd_constructor_case made instruction (.I64x2ShrS dst a entry)
  · simd_constructor_case made instruction (.I64x2ShrU dst a entry)
  · simd_constructor_case made instruction (.I64x2Add dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction

private theorem make_simd_roundtrip_208 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 208 ≤ op.val) (upper : op.val < 224)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 208 ≤ n at lower
  change n < 224 at upper
  interval_cases n
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I64x2Sub dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.I64x2Mul dst a entry)
  · simd_constructor_case made instruction (.I64x2Eq dst a entry)
  · simd_constructor_case made instruction (.I64x2Ne dst a entry)
  · simd_constructor_case made instruction (.I64x2LtS dst a entry)
  · simd_constructor_case made instruction (.I64x2GtS dst a entry)
  · simd_constructor_case made instruction (.I64x2LeS dst a entry)
  · simd_constructor_case made instruction (.I64x2GeS dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtmulLowI32x4S dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtmulHighI32x4S dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtmulLowI32x4U dst a entry)
  · simd_constructor_case made instruction (.I64x2ExtmulHighI32x4U dst a entry)

private theorem make_simd_roundtrip_224 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 224 ≤ op.val) (upper : op.val < 240)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 224 ≤ n at lower
  change n < 240 at upper
  interval_cases n
  · simd_constructor_case made instruction (.F32x4Abs dst a entry)
  · simd_constructor_case made instruction (.F32x4Neg dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.F32x4Sqrt dst a entry)
  · simd_constructor_case made instruction (.F32x4Add dst a entry)
  · simd_constructor_case made instruction (.F32x4Sub dst a entry)
  · simd_constructor_case made instruction (.F32x4Mul dst a entry)
  · simd_constructor_case made instruction (.F32x4Div dst a entry)
  · simd_constructor_case made instruction (.F32x4Min dst a entry)
  · simd_constructor_case made instruction (.F32x4Max dst a entry)
  · simd_constructor_case made instruction (.F32x4Pmin dst a entry)
  · simd_constructor_case made instruction (.F32x4Pmax dst a entry)
  · simd_constructor_case made instruction (.F64x2Abs dst a entry)
  · simd_constructor_case made instruction (.F64x2Neg dst a entry)
  · change Result.ok (none : Option runtime.bytecode.Instr) = Result.ok (some instruction) at made
    simp only [Result.ok.injEq] at made
    contradiction
  · simd_constructor_case made instruction (.F64x2Sqrt dst a entry)

private theorem make_simd_roundtrip_240 (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (lower : 240 ≤ op.val) (upper : op.val < 256)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 240 ≤ n at lower
  change n < 256 at upper
  interval_cases n
  · simd_constructor_case made instruction (.F64x2Add dst a entry)
  · simd_constructor_case made instruction (.F64x2Sub dst a entry)
  · simd_constructor_case made instruction (.F64x2Mul dst a entry)
  · simd_constructor_case made instruction (.F64x2Div dst a entry)
  · simd_constructor_case made instruction (.F64x2Min dst a entry)
  · simd_constructor_case made instruction (.F64x2Max dst a entry)
  · simd_constructor_case made instruction (.F64x2Pmin dst a entry)
  · simd_constructor_case made instruction (.F64x2Pmax dst a entry)
  · simd_constructor_case made instruction (.I32x4TruncSatF32x4S dst a entry)
  · simd_constructor_case made instruction (.I32x4TruncSatF32x4U dst a entry)
  · simd_constructor_case made instruction (.F32x4ConvertI32x4S dst a entry)
  · simd_constructor_case made instruction (.F32x4ConvertI32x4U dst a entry)
  · simd_constructor_case made instruction (.I32x4TruncSatF64x2SZero dst a entry)
  · simd_constructor_case made instruction (.I32x4TruncSatF64x2UZero dst a entry)
  · simd_constructor_case made instruction (.F64x2ConvertLowI32x4S dst a entry)
  · simd_constructor_case made instruction (.F64x2ConvertLowI32x4U dst a entry)

theorem make_simd_roundtrip_bounded (op dst a entry : U32) (instruction : runtime.bytecode.Instr)
    (bounded : op.val < 256)
    (made : runtime.bytecode.Instr.make_simd op dst a entry = Result.ok (some instruction)) :
    runtime.bytecode.Instr.simd instruction = Result.ok (some (op,dst,a,entry)) := by
  by_cases h0 : op.val < 16
  · exact make_simd_roundtrip_0 op dst a entry instruction (by omega) h0 made
  by_cases h16 : op.val < 32
  · exact make_simd_roundtrip_16 op dst a entry instruction (by omega) h16 made
  by_cases h32 : op.val < 48
  · exact make_simd_roundtrip_32 op dst a entry instruction (by omega) h32 made
  by_cases h48 : op.val < 64
  · exact make_simd_roundtrip_48 op dst a entry instruction (by omega) h48 made
  by_cases h64 : op.val < 80
  · exact make_simd_roundtrip_64 op dst a entry instruction (by omega) h64 made
  by_cases h80 : op.val < 96
  · exact make_simd_roundtrip_80 op dst a entry instruction (by omega) h80 made
  by_cases h96 : op.val < 112
  · exact make_simd_roundtrip_96 op dst a entry instruction (by omega) h96 made
  by_cases h112 : op.val < 128
  · exact make_simd_roundtrip_112 op dst a entry instruction (by omega) h112 made
  by_cases h128 : op.val < 144
  · exact make_simd_roundtrip_128 op dst a entry instruction (by omega) h128 made
  by_cases h144 : op.val < 160
  · exact make_simd_roundtrip_144 op dst a entry instruction (by omega) h144 made
  by_cases h160 : op.val < 176
  · exact make_simd_roundtrip_160 op dst a entry instruction (by omega) h160 made
  by_cases h176 : op.val < 192
  · exact make_simd_roundtrip_176 op dst a entry instruction (by omega) h176 made
  by_cases h192 : op.val < 208
  · exact make_simd_roundtrip_192 op dst a entry instruction (by omega) h192 made
  by_cases h208 : op.val < 224
  · exact make_simd_roundtrip_208 op dst a entry instruction (by omega) h208 made
  by_cases h224 : op.val < 240
  · exact make_simd_roundtrip_224 op dst a entry instruction (by omega) h224 made
  exact make_simd_roundtrip_240 op dst a entry instruction (by omega) bounded made

end Itasca.Runtime.Code
