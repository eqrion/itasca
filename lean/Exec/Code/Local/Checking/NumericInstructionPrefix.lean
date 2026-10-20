import Exec.Code.Local.Checking.OpenInstructionCompiler
import Exec.Code.Local.Lowering.Common.NumericInstructionPublication
import Exec.Code.Local.Lowering.Table.ScalarTablePreservation

namespace Exec.Code
open Aeneas Aeneas.Std Abs.Numeric

/-- Observation preserves every instruction's operand check and pending branch
owner, including in an unreachable source region. -/
theorem compiler_observe_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have stable := compiler_observe_stable ops law before after state called
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have growth : InstructionCheckExtends before.function after.function := by
    refine ⟨stable.capacity,?_,?_,?_,?_,?_⟩ <;> rw [frame] <;> exact le_rfl
  have same : after.function.code.val = before.function.code.val := by rw [frame]
  refine held.append growth ?_ [] (by simpa using same) (by simp)
  intro index owned
  have frames : after.frames = before.frames := by rw [frame]
  simpa only [PendingInstructionSite,frames] using owned

/-- Every actual live integer callback retains checks of all earlier stored
instructions and constructs the new instruction's check from source layout. -/
theorem compiler_numeric_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Instruction)
    (layout : CompilerLayout before (front ++ List.replicate op.arity (integerType op.input)))
    (live : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [integerType op.output])
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have checked := compiler_numeric_lowered_checked ops law before state types front op layout live concrete typed codeFits sourceFits coordinateFits
  rw [called,WP.spec_ok] at checked
  obtain ⟨left,right,lowered,valid⟩ := checked rfl
  have frames := (compiler_numeric_ordinary_result ops law before after state op (.Ok ()) called).frames
  apply lowered.openInstructionPrefix (compiler_numeric_tables ops law before after state op called) held (valid := valid)
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Exec.Code
