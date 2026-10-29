import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentProgram
import Itasca.Runtime.Spec.SegmentInitCases

/-!
Source instructions represented by the straight-line segment bytecode.

Main declarations: `segmentInstructionSource` and `segmentSource`. A direct consumer is `Compiler.Local.Relations.Segments.SegmentFlowSource`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std SpecExt

/-- Source instructions represented by the straight-line segment bytecode. -/
def segmentInstructionSource (code : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → List admininstr
  | .Const32 _ bits => [Spec.Segment.i32 bits.val]
  | .GlobalGet _ index => [.GLOBAL_GET (.mk_uN index.val)]
  | .MemoryInit _ index => [.MEMORY_INIT (.mk_uN index.val)]
  | .TableInit _ entry =>
      let pair := code.indirect.val[entry.val]!
      [.TABLE_INIT (.mk_uN pair.2.val) (.mk_uN pair.1.val)]
  | .DataDrop index => [.DATA_DROP (.mk_uN index.val)]
  | .ElemDrop index => [.ELEM_DROP (.mk_uN index.val)]
  | _ => []

def segmentSource (code : runtime.bytecode.CompiledFunction) (instructions : List runtime.bytecode.Instr) : List admininstr :=
  instructions.flatMap (segmentInstructionSource code)

/-- The pending operand count is a syntactic property of emitted segment groups. -/
inductive SegmentFlow : Nat → List runtime.bytecode.Instr → Prop where
  | done : SegmentFlow 0 [.Return 0#u32 0#u32]
  | constant (pending : Nat) (dst bits : U32) (rest : List runtime.bytecode.Instr)
      (slot : dst.val = pending) (bound : pending < 3) (next : SegmentFlow (pending+1) rest) :
      SegmentFlow pending (.Const32 dst bits :: rest)
  | global (index : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 1 rest) :
      SegmentFlow 0 (.GlobalGet 0#u32 index :: rest)
  | memory (data : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 3 (.MemoryInit 0#u32 data :: rest)
  | table (entry : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 3 (.TableInit 0#u32 entry :: rest)
  | dataDrop (data : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 0 (.DataDrop data :: rest)
  | elementDrop (element : U32) (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
      SegmentFlow 0 (.ElemDrop element :: rest)

theorem segmentSource_wf (code : runtime.bytecode.CompiledFunction) (instructions : List runtime.bytecode.Instr) :
    Forall wf_admininstr (segmentSource code instructions) := by
  intro instruction member
  obtain ⟨raw, _, member⟩ := List.mem_flatMap.mp member
  unfold segmentInstructionSource at member
  split at member <;> simp only [List.mem_singleton,List.not_mem_nil] at member
  all_goals subst instruction
  · exact Spec.Segment.i32_wf _ (by scalar_tac)
  · exact .admininstr_case_46 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_66 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_54 _ _ (Spec.Segment.index_wf _ (by scalar_tac)) (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_67 _ (Spec.Segment.index_wf _ (by scalar_tac))
  · exact .admininstr_case_55 _ (Spec.Segment.index_wf _ (by scalar_tac))

end Itasca.Runtime.Code
