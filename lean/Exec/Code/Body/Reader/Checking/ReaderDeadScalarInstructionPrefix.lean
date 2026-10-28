import Exec.Code.Body.Reader.Acceptance.ScalarReaderAcceptance
import Exec.Code.Body.Reader.Publication.ScalarCallbackPublication
import Exec.Code.Local.Checking.DeadInstructionPrefix
import Exec.Code.Local.Checking.TerminalInstructionPrefix
import Exec.Code.Local.Checking.ScalarExitSlotBounds
import Exec.Code.Local.Callbacks.Common.CompilerTerminalMetadata

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- All scalar source reader kinds preserve both checks in unreachable code.
Literal bits and local/global indices are exactly those selected by the reader. -/
theorem reader_dead_scalar_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (kind : ScalarReaderKind)
    (dead : before.reachable = false)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  rw [kind.dispatch] at accepted
  obtain ⟨value,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
  by_cases trap : kind = .unreachable
  · subst kind
    exact ⟨compiler_unreachable_open_instructions ops law before after out codeFits sourceFits coordinateFits held callback,
      (compiler_unreachable_ordinary_result ops law before after out (.Ok ()) callback).exit_slots exits⟩
  · have supported : ScalarPublicationAction (kind.action value) := by
      cases kind <;> first | contradiction | constructor
    obtain ⟨opcode,a,b,bits,_,dispatch⟩ := scalar_hook_publication_dispatch ops before out supported
    rw [dispatch] at callback
    exact compiler_dead_op_checked_prefix ops law before after out opcode a b bits dead held exits callback

end Itasca.Runtime.Code
