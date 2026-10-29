import Itasca.Runtime.Compiler.Local.Capacity.SimdMeaningBound
import Mathlib.Tactic.IntervalCases
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
