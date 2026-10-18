import Exec.Code.Local.Capacity.AuxiliaryGrowth
import Exec.Code.Local.Lowering.Table.ScalarTablePreservation
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
namespace Exec.Code
open Aeneas Aeneas.Std

theorem compiler_numeric_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state
      (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) : AuxiliaryGrowth before after :=
  .of_tables (compiler_numeric_tables ops law before after state op accepted)
    (compiler_numeric_code_mono ops law before after state op accepted)

theorem compiler_float_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state
      (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) : AuxiliaryGrowth before after :=
  .of_tables (compiler_float_tables ops law before after state op accepted)
    (compiler_float_code_mono ops law before after state op accepted)

theorem compiler_core_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state
      op.opcode op.first op.second 0#u128 = .ok (.Ok (),after)) : AuxiliaryGrowth before after :=
  .of_tables (compiler_core_tables ops law before after state op accepted)
    (compiler_core_code_mono ops law before after state op accepted)

end Exec.Code
