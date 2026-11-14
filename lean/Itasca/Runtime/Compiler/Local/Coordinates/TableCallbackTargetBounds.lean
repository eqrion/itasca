import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarTargetEffects
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerTableScratchSimd
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects

/-!
Sections, each formerly its own module: LoweringTargetBounds, TableCallbackTargetBounds.
-/

/-! ## LoweringTargetBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual numeric lowering retains every existing jump-table target bound. -/
theorem compiler_numeric_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction) (held : JumpTableBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    JumpTableBounds after :=
  held.retained (after := after)
    (congrArg CompilerTables.jumpTables (compiler_numeric_tables ops law before after state op called))
    (compiler_numeric_code_mono ops law before after state op called)

/-- Actual float lowering retains every existing jump-table target bound. -/
theorem compiler_float_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction) (held : JumpTableBounds before)
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

end Itasca.Runtime.Compiler

end

/-! ## TableCallbackTargetBounds -/

section

/-!
Branch-table target bounds from strict branch-code growth through the target loop and callback. The result bounds every published jump-table target.
-/

/-! ## Branch Code Strict -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- A successful actual branch always emits at least one control instruction,
including loop targets and copies elided by the compiler. -/
theorem compiler_branch_code_strict {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    before.function.code.val.length < after.function.code.val.length := by
  exact (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional
    (.Ok ()) called).code_strict law

end Itasca.Runtime.Compiler

end

/-! ## Table Target Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A table stub records its PC before lowering its branch. Actual branch code
then grows strictly, putting the recorded target inside the resulting vector. -/
theorem compiler_table_branch_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : JumpTableBounds before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨target,budget,table,position,appended,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  have growth := compiler_branch_code_strict ops law staged after depth 1#u32 false branch
  have tables := congrArg CompilerTables.jumpTables (compiler_branch_tables ops law staged after depth 1#u32 false branch)
  change after.function.jump_tables.val = table.val at tables
  intro entry member
  rw [tables,appended] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with prior | rfl
  · exact (held entry prior).trans (by simpa only [staged] using growth)
  · simpa only [position,staged] using growth

/-- Every actual branch in the finite lowering loop retains bounded targets. -/
theorem TableBranchRun.jump_table_bounds {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) (held : JumpTableBounds before) :
    JumpTableBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inbounds called rest ih =>
    let depth := before.table_depths.val[index.val]
    exact ih (compiler_table_branch_target_bounds ops law before middle index depth
      (List.getElem?_eq_getElem inbounds) held called)

/-- The actual dispatch emission and complete stub loop establish all jump-table
bounds without assuming loop acceptance or a completed code certificate. -/
theorem compiler_lower_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : JumpTableBounds before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  exact run.jump_table_bounds law (emission.jump_table_bounds held)

end Itasca.Runtime.Compiler

end

/-! ## Table Callback Target Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Streamed labels retain all jump-table targets and code. -/
theorem compiler_table_label_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : JumpTableBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  simpa only [JumpTableBounds,frame] using held

/-- The actual final branch-table callback retains all jump-target bounds. -/
theorem compiler_br_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : JumpTableBounds after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) called with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : JumpTableBounds labeled := by
      rw [frame]
      exact held
    have loweredCoordinates := compiler_lower_table_target_bounds ops law labeled lowered coordinates lowerCall
    exact compiler_observe_jump_table_bounds ops law {lowered with reachable := false, table_depths := cleared} after state
      (by simpa only [JumpTableBounds] using loweredCoordinates) observed
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have coordinates : JumpTableBounds labeled := by
      rw [frame]
      exact held
    exact compiler_observe_jump_table_bounds ops law {labeled with table_depths := cleared} after state
      (by simpa only [JumpTableBounds] using coordinates) observed

end Itasca.Runtime.Compiler

end

end
