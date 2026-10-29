import Itasca.Runtime.Compiler.Local.Publication.OrdinaryMapPublication
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneScalar
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneStateful
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEffects

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual numeric lowering preserves all control-map bounds. -/
theorem compiler_numeric_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction)
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
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
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

end Itasca.Runtime.Compiler
