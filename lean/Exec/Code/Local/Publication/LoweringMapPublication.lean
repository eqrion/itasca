import Exec.Code.Local.Publication.OrdinaryMapPublication
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneStateful
import Exec.Code.Local.Relations.Common.StatefulEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual numeric lowering preserves all control-map bounds. -/
theorem compiler_numeric_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_numeric_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_numeric_code_mono ops law before after state op called)
  rw [compiler_numeric_cursor ops law before after state op called]
  exact forward

/-- Actual float lowering preserves all control-map bounds. -/
theorem compiler_float_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_float_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_float_code_mono ops law before after state op called)
  rw [compiler_float_cursor ops law before after state op called]
  exact forward

/-- Actual core lowering preserves all control-map bounds. -/
theorem compiler_core_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_core_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_core_code_mono ops law before after state op called)
  rw [compiler_core_cursor ops law before after state op called]
  exact forward

end Itasca.Runtime.Code
