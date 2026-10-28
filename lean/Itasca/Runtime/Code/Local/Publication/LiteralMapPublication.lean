import Itasca.Runtime.Code.Local.Publication.OrdinaryMapPublication
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Code.Local.Lowering.Common.LiteralCursor
import Itasca.Runtime.Code.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneStateful
import Itasca.Runtime.Code.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- SIMD dispatch retains map bounds in live and dead code. -/
theorem compiler_lower_simd_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  obtain ⟨stable,_,cursor,_⟩ := compiler_lower_simd_effects ops law before after state opcode a b bits lower upper called
  apply held.ordinary stable (compiler_lower_simd_code_mono ops law before after state opcode a b bits lower upper called)
  rw [cursor]
  exact forward

end Itasca.Runtime.Code
