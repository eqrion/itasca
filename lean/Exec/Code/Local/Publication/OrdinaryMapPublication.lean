import Exec.Code.Local.Publication.ControlMapPublication
import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotone
import Exec.Code.Local.Source.SourceCursor

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Ordinary callbacks retain map entries and owners. Code growth and source
progress are enough to preserve their publication bounds. -/
theorem ControlMapPublication.ordinary {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerOrdinaryStable before after)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  apply held.retained stable.stable stable.controls _ code cursor
  simp only [activeControlMaps,stable.frames]

/-- Actual bytecode emission retains all control-map bounds. -/
theorem compiler_emit_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (held : ControlMapPublication before)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_emit_ordinary_result ops before after instruction (.Ok ()) called)
    (compiler_emit_code_mono ops law before after instruction (.Ok ()) called)
  rw [compiler_emit_cursor ops before after instruction (.Ok ()) called]

/-- Actual observation preserves control-map bounds while advancing the reader cursor. -/
theorem compiler_observe_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_observe_ordinary_result ops law before after state (.Ok ()) called)
    (compiler_observe_code_mono ops law before after state (.Ok ()) called)
  rw [compiler_observe_cursor ops law before after state (.Ok ()) called rfl]
  exact forward

end Itasca.Runtime.Code
