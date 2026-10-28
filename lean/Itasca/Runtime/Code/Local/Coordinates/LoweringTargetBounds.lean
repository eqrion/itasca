import Itasca.Runtime.Code.Local.Source.JumpTableBounds
import Itasca.Runtime.Code.Local.Coordinates.ScalarTargetEffects
import Itasca.Runtime.Code.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdStaticTables
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneScalar
import Itasca.Runtime.Code.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Itasca.Runtime.Code.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual numeric lowering retains every existing jump-table target bound. -/
theorem compiler_numeric_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_numeric_tables ops law before after state op called))
    (compiler_numeric_code_mono ops law before after state op called)

/-- Actual float lowering retains every existing jump-table target bound. -/
theorem compiler_float_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_float_tables ops law before after state op called))
    (compiler_float_code_mono ops law before after state op called)

/-- Actual core lowering retains every existing jump-table target bound. -/
theorem compiler_core_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (op.opcode) op.first op.second 0#u128 = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_core_tables ops law before after state op called))
    (compiler_core_code_mono ops law before after state op called)

/-- Scalar calls, constants, references and bulk operations retain target bounds. -/
theorem compiler_scalar_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨tables,growth⟩ := compiler_scalar_target_effects ops law before after state opcode a b bits supported called
  exact held.retained (after := after) tables growth

/-- Every SIMD lowering preserves the jump table and grows code monotonically. -/
theorem compiler_simd_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (compiler_lower_simd_preserved_tables ops law before after state opcode a b bits lower upper called).2
    (compiler_lower_simd_code_mono ops law before after state opcode a b bits lower upper called)

/-- Frame entry retains targets independently of live or dormant source layout. -/
theorem compiler_enter_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (held : JumpTableBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_enter_tables ops law before after state kind bt called))
    (compiler_enter_code_mono ops law before after state kind bt called)

/-- Scope close patches instructions and retains the recorded target vector. -/
theorem compiler_end_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_end_tables ops law before after state kind bt called))
    (compiler_end_code_mono ops law before after state kind bt called)

end Itasca.Runtime.Code
