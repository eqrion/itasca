import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerTableScratchSimd
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: SimdSourceShape, SimdPureSignature, SimdSourceSignature, SimdBits, SimdEffects.
-/

/-! ## SimdSourceShape -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Runtime word widths, read from the independently typed source signature. -/
def simdSourceWidth : Option valtype → U32
  | none => 0#u32
  | some .V128 => 2#u32
  | some _ => 1#u32

def simdSourceShape (input output : List valtype) : U32 × U32 × U32 × U32 :=
  (simdSourceWidth input[0]?,simdSourceWidth input[1]?,simdSourceWidth input[2]?,simdSourceWidth output[0]?)

private def PureShapeCorrect (opcode : U32) : Prop :=
  match pureMeaning opcode.val with
  | none => True
  | some op => runtime.bytecode.simd_shape opcode = .ok (some (simdSourceShape op.signature.inputs op.signature.outputs))

private theorem pure_shape_table (opcode : U32) (bounded : opcode.val < 256) : PureShapeCorrect opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n <;> with_unfolding_all (first | rfl | exact True.intro)

private def LaneShapeCorrect (opcode : U32) : Prop :=
  match laneMeaning opcode.val with
  | none => True
  | some op => runtime.bytecode.simd_shape opcode = .ok (some (simdSourceShape op.inputs op.outputs))

private theorem lane_shape_table (opcode : U32) (bounded : opcode.val < 256) : LaneShapeCorrect opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n <;> with_unfolding_all (first | rfl | exact True.intro)

private def MemoryShapeCorrect (opcode : U32) : Prop :=
  match memoryMeaning opcode.val with
  | none => True
  | some op => runtime.bytecode.simd_shape opcode = .ok (some (simdSourceShape op.inputs op.outputs))

private theorem memory_shape_table (opcode : U32) (bounded : opcode.val < 256) : MemoryShapeCorrect opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n <;> with_unfolding_all (first | rfl | exact True.intro)

theorem SimdImmediateMeaning.shape {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) :
    runtime.bytecode.simd_shape opcode = .ok (some (simdSourceShape input output)) := by
  have bounded := meaning.opcode_bound
  cases meaning with
  | pure opcode immediate op meaning =>
    have correct := pure_shape_table opcode bounded
    unfold PureShapeCorrect at correct
    simpa only [meaning] using correct
  | lane opcode immediate op meaning lane position =>
    have correct := lane_shape_table opcode bounded
    unfold LaneShapeCorrect at correct
    simpa only [meaning] using correct
  | memory opcode immediate op meaning argument lane memory available offset position =>
    have correct := memory_shape_table opcode bounded
    unfold MemoryShapeCorrect at correct
    simpa only [meaning] using correct
  | shuffle => with_unfolding_all rfl
end Itasca.Runtime.Compiler

end

/-! ## SimdPureSignature -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def simdPureOutput (signature : Signature) : valtype :=
  match signature with | .test => .I32 | _ => .V128

private def PureSignatureCorrect (opcode : U32) : Prop :=
  match pureMeaning opcode.val with
  | none => True
  | some op => SourceMachine.Simd.PureSignature op.instruction op.signature.inputs (simdPureOutput op.signature)

private theorem pure_signature_table (opcode : U32) (bounded : opcode.val < 256) :
    PureSignatureCorrect opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n <;> with_unfolding_all (first | exact True.intro | constructor)

theorem pure_source_signature {opcode : U32} {op : Operation}
    (meaning : pureMeaning opcode.val = some op) :
    SourceMachine.Simd.PureSignature op.instruction op.signature.inputs (simdPureOutput op.signature) := by
  have table := pure_signature_table opcode (pure_bound meaning)
  unfold PureSignatureCorrect at table
  simpa only [meaning] using table

end Itasca.Runtime.Compiler

end

/-! ## SimdSourceSignature -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def simdLaneOutput (op : LaneOperation) : valtype :=
  if op.replace then .V128 else valtype_numtype op.scalar

theorem lane_source_signature (op : LaneOperation) (lane : laneidx) :
    SourceMachine.Simd.PureSignature (op.instruction lane) op.inputs (simdLaneOutput op) := by
  cases op <;> with_unfolding_all constructor

theorem memory_source_signature (op : MemoryOperation) (argument : memarg) (lane : laneidx) :
    SourceMachine.Simd.MemorySignature (op.instruction argument lane) op.inputs op.outputs := by
  cases op <;> with_unfolding_all constructor

theorem SimdImmediateMeaning.allowed {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : SourceMachine.SimdInstr source := by
  cases meaning with
  | pure opcode immediate op meaning => exact .pure (pure_source_signature meaning)
  | lane opcode immediate op meaning lane position => exact .pure (lane_source_signature op _)
  | memory opcode immediate op meaning argument lane memory available offset position =>
    exact .memory (memory_source_signature op argument _)
  | shuffle immediate low high bits => with_unfolding_all exact SourceMachine.SimdInstr.pure (.shuffle _ _)

theorem SimdEmission.allowed {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after) : SourceMachine.SimdInstr source := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata made position =>
    exact meaning.allowed
  | constant => exact .constant _
end Itasca.Runtime.Compiler

end

/-! ## SimdBits -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Packing a vector constant retains the full low and high words. -/
theorem initializer_bits_val (lo hi : U64) :
    (initializerBits lo hi).val = lo.val + hi.val * 2^64 := by
  have hlo : lo.val < 2^64 := by scalar_tac
  have hloWide : lo.val < 2^128 := by scalar_tac
  have hhiWide : hi.val < 2^128 := by scalar_tac
  have hshift : hi.val * 2^64 < 2^128 := by scalar_tac
  change (lo.bv.setWidth 128 ||| (hi.bv.setWidth 128 <<< 64)).toNat = lo.val + hi.val * 2^64
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_setWidth,UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt hloWide,Nat.mod_eq_of_lt hhiWide,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hshift]
  rw [Nat.or_comm,←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt hlo,Nat.shiftLeft_eq]
  omega
end Itasca.Runtime.Compiler

end

/-! ## SimdEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

section
variable {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
  (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
  (opcode : U16) (a : U32) (bits : U128)
  (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after))

include accepted law

theorem compiler_simd_sources : SourceProgress before after := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' sources_step accepted using ops, law

theorem compiler_simd_cursor : after.next_source = state.pos := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' cursor_step accepted using ops, law

theorem compiler_simd_capacity : CapacityStep before after state := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' capacity_step accepted using ops, law
end

/-- The actual callback path retains source and capacity facts in both live
and dormant code; no SIMD allocation premise is supplied. -/
theorem compiler_lower_simd_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
      after.next_source = state.pos ∧ CapacityStep before after state := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact ⟨compiler_simd_ordinary_result ops law before after state opcode a bits (.Ok ()) accepted,
      compiler_simd_sources ops law before after state opcode a bits accepted,
      compiler_simd_cursor ops law before after state opcode a bits accepted,
      compiler_simd_capacity ops law before after state opcode a bits accepted⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    have capacity := compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted
    exact ⟨compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted,
      compiler_observe_sources ops law before after state (.Ok ()) accepted,
      compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl,
      capacity.1,capacity.2 rfl⟩
end Itasca.Runtime.Compiler

end
