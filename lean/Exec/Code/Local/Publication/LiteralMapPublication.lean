import Exec.Code.Local.Publication.OrdinaryMapPublication
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneLiteral
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Relations.Calls.IndirectCallMetadata
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneStateful
import Exec.Code.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Exec.Code.Local.Lowering.Simd.SimdEffects

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual op65 lowering retains all control-map publication bounds. -/
theorem compiler_op65_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op65_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op65_code_mono ops law before after state a b bits called)
  rw [compiler_op65_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op66 lowering retains all control-map publication bounds. -/
theorem compiler_op66_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op66_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op66_code_mono ops law before after state a b bits called)
  rw [compiler_op66_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op32 lowering retains all control-map publication bounds. -/
theorem compiler_op32_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op32_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op32_code_mono ops law before after state a b bits called)
  rw [compiler_op32_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op33 lowering retains all control-map publication bounds. -/
theorem compiler_op33_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op33_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op33_code_mono ops law before after state a b bits called)
  rw [compiler_op33_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op34 lowering retains all control-map publication bounds. -/
theorem compiler_op34_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op34_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op34_code_mono ops law before after state a b bits called)
  rw [compiler_op34_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op16 lowering retains all control-map publication bounds. -/
theorem compiler_op16_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op16_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op16_code_mono ops law before after state a b bits called)
  rw [compiler_op16_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op1 lowering retains all control-map publication bounds. -/
theorem compiler_op1_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op1_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op1_code_mono ops law before after state a b bits called)
  rw [compiler_op1_cursor ops law before after state a b bits called]
  exact forward

/-- Actual op26 lowering retains all control-map publication bounds. -/
theorem compiler_op26_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_op26_ordinary_result ops law before after state a b bits (.Ok ()) called)
    (compiler_op26_code_mono ops law before after state a b bits called)
  rw [compiler_op26_cursor ops law before after state a b bits called]
  exact forward

/-- Actual indirect_call lowering retains all control-map publication bounds. -/
theorem compiler_indirect_call_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_indirect_call_ordinary_result ops law before after state a b (.Ok ()) called)
    (compiler_indirect_call_code_mono ops law before after state a b (.Ok ()) called)
  rw [compiler_indirect_call_cursor ops law before after state a b called]
  exact forward

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

end Exec.Code
