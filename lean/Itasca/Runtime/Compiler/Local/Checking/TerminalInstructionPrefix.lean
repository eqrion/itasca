import Itasca.Runtime.Compiler.Local.Checking.NumericInstructionPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CallbackTables
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Ordinary append effects preserve all older checks when frame ownership is
unchanged, including terminal callbacks that subsequently become unreachable. -/
theorem CompilerInstructionPrefix.append_with_frames {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} (held : CompilerInstructionPrefix before)
    (growth : InstructionCheckExtends before.function after.function) (frames : after.frames = before.frames)
    (fragment : List runtime.bytecode.Instr) (code : after.function.code.val = before.function.code.val++fragment)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CompilerInstructionPrefix after := by
  refine held.append growth ?_ fragment code fresh
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

/-- The trap callback checks its emitted trap instruction, or emits no code
when the source prefix is already unreachable. -/
theorem compiler_unreachable_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_unreachable_tables ops law before after state called)
    (compiler_unreachable_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_unreachable_code_mono ops law before after state called)
  cases live : before.reachable with
  | false =>
    have effect := callback_unreachable_dead ops law before state live
    rw [called,WP.spec_ok] at effect
    dsimp only at effect
    exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)
  | true =>
    have effect := callback_unreachable ops law before state live codeFits sourceFits coordinateFits
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,code,frames,_⟩ := effect rfl
    apply held.append_with_frames growth frames [.Unreachable] code
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact CoreInstructionBounds.accepts .unreachable

/-- Live RETURN's source suffix fits the current frame; later observation
retains that capacity and every previously stored instruction check. -/
theorem compiler_return_live_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (live : before.reachable = true) (bodyFrame : before.frames.val[0]? = some body)
    (height : before.height.val = source.val+body.results.val)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return ops law before state body source live bodyFrame height codeFits sourceFits coordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,code,frames,_⟩ := effect rfl
  apply held.append_with_frames growth frames [.Return source body.results] code
  intro instruction member
  simp only [List.mem_singleton] at member
  subst instruction
  exact (CoreInstructionBounds.return_ (by have capacity := growth.slots; omega)).accepts

/-- A return in dead source code only observes the source stack. -/
theorem compiler_return_dead_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_return_tables ops law before after state called)
    (compiler_return_stable_result ops law before after state (.Ok ()) called).capacity
    (compiler_return_code_mono ops law before after state called)
  have effect := callback_return_dead ops law before state dead
  rw [called,WP.spec_ok] at effect
  dsimp only at effect
  exact held.append_with_frames growth (by rw [effect]) [] (by simpa using congrArg alloc.vec.Vec.val effect.code) (by simp)

end Itasca.Runtime.Compiler
