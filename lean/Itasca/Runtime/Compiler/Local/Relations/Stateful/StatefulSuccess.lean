import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Generated.Types
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix

/-!
Sections, each formerly its own module: StatefulOpcode, StatefulLowering, StatefulSuccess.
-/

/-! ## StatefulOpcode -/

section

/-!
Expanded opcodes use 0x100 plus the misc-prefix subopcode.

Main declarations: `statefulOpcode` and `statefulArguments`. A direct consumer is `Compiler.Local.Relations.Calls.StatefulCallbacks`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Expanded opcodes use 0x100 plus the misc-prefix subopcode. -/
def statefulOpcode : SourceMachine.Stateful.Instruction → U16
  | .refNull _ => 208#u16
  | .refFunc _ => 210#u16
  | .refIsNull => 209#u16
  | .tableGet _ => 37#u16
  | .tableSet _ => 38#u16
  | .tableSize _ => 272#u16
  | .tableGrow _ => 271#u16
  | .tableFill _ => 273#u16
  | .tableCopy .. => 270#u16
  | .tableInit .. => 268#u16
  | .elemDrop _ => 269#u16
  | .memorySize => 63#u16
  | .memoryGrow => 64#u16
  | .memoryFill => 267#u16
  | .memoryCopy => 266#u16
  | .memoryInit _ => 264#u16
  | .dataDrop _ => 265#u16

/-- Callback arguments, including the reversed table.init pair order. -/
def statefulArguments : SourceMachine.Stateful.Instruction → Nat × Nat
  | .refNull .FUNCREF => (0, 0)
  | .refNull .EXTERNREF => (1, 0)
  | .refFunc index | .tableGet index | .tableSet index | .tableSize index
    | .tableGrow index | .tableFill index | .elemDrop index | .memoryInit index
    | .dataDrop index => (index, 0)
  | .tableCopy destination source => (destination, source)
  | .tableInit table element => (element, table)
  | _ => (0, 0)

def StatefulArguments (op : SourceMachine.Stateful.Instruction) (a b : U32) : Prop :=
  a.val = (statefulArguments op).1 ∧ b.val = (statefulArguments op).2

/-- Exact bytecode constructor. `first` starts the complete operand suffix;
`second` is the next scalar slot. `entry` indexes the retained pair table. -/
def statefulInstruction (op : SourceMachine.Stateful.Instruction) (first second a entry : U32) :
    runtime.bytecode.Instr :=
  match op with
  | .refNull _ => .RefNull first
  | .refFunc _ => .RefFunc first a
  | .refIsNull => .RefIsNull first first
  | .tableGet _ => .TableGet first first a
  | .tableSet _ => .TableSet first second a
  | .tableSize _ => .TableSize first a
  | .tableGrow _ => .TableGrow first a
  | .tableFill _ => .TableFill first a
  | .tableCopy .. => .TableCopy first entry
  | .tableInit .. => .TableInit first entry
  | .elemDrop _ => .ElemDrop a
  | .memorySize => .MemorySize first
  | .memoryGrow => .MemoryGrow first
  | .memoryFill => .MemoryFill first
  | .memoryCopy => .MemoryCopy first
  | .memoryInit _ => .MemoryInit first a
  | .dataDrop _ => .DataDrop a

/-- Pair-table entries are function-local immutable compiler metadata. -/
def StatefulPair (pairs : List (U32 × U32)) (op : SourceMachine.Stateful.Instruction)
    (a b entry : U32) : Prop :=
  match op with
  | .tableCopy .. | .tableInit .. => pairs[entry.val]? = some (a, b)
  | _ => True

end Itasca.Runtime.Compiler

end

/-! ## StatefulLowering -/

section

/-!
Depth, pair-table use and dispatch equations for stateful lowering.

Main declarations: `StatefulReads` and `lower_stateful_eq`. A direct consumer is `Compiler.Local.Relations.Stateful.StatefulEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result
set_option maxRecDepth 4096

def statefulDepth (op : SourceMachine.Stateful.Instruction) : Usize :=
  match op.arity with
  | 0 => 0#usize
  | 1 => 1#usize
  | 2 => 2#usize
  | _ => 3#usize

def statefulUsesPair : SourceMachine.Stateful.Instruction → Bool
  | .tableCopy .. | .tableInit .. => true
  | _ => false

def StatefulReads {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (op : SourceMachine.Stateful.Instruction)
    (first second : U32) : Prop :=
  (if op.arity = 0 then first = compiler.height else
    runtime.compiler.FunctionCompiler.operand ops compiler (statefulDepth op) = .ok (.Ok first)) ∧
  (∀ table, op = .tableSet table →
    runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok second))

noncomputable def statefulLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (a b : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  match op with
  | .refNull _ =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.RefNull compiler.height)
  | .refFunc _ =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.RefFunc compiler.height a)
  | .refIsNull =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state (runtime.bytecode.Instr.RefIsNull val val1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r1, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .tableGet _ =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state (runtime.bytecode.Instr.TableGet val val1 a)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r1, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .tableSet _ =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        2#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state (runtime.bytecode.Instr.TableSet val val1 a)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .tableSize _ =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.TableSize compiler.height a)
  | .tableGrow _ =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        2#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.TableGrow val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .tableFill _ =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.TableFill val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .tableCopy .. =>
    let (r, paired) ←
      runtime.compiler.FunctionCompiler.pair ops compiler a b
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops paired
          3#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          paired state (runtime.bytecode.Instr.TableCopy val1 val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r2, paired)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, paired)
  | .tableInit .. =>
    let (r, paired) ←
      runtime.compiler.FunctionCompiler.pair ops compiler a b
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops paired
          3#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          paired state (runtime.bytecode.Instr.TableInit val1 val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r2, paired)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, paired)
  | .elemDrop _ =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.ElemDrop a)
  | .memorySize =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.MemorySize compiler.height)
  | .memoryGrow =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.MemoryGrow val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .memoryFill =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.MemoryFill val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .memoryCopy =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.MemoryCopy val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .memoryInit _ =>
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        compiler state (runtime.bytecode.Instr.MemoryInit val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | .dataDrop _ =>
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
      state (runtime.bytecode.Instr.DataDrop a)

theorem lower_stateful_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (a b : U32) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128 =
      statefulLowering ops compiler state op a b := by
  cases op with
  | refNull _ => exact runtime.compiler.lower.FunctionCompiler.op.ref_null ops compiler state a b 0#u128 reachable
  | refFunc _ => exact runtime.compiler.lower.FunctionCompiler.op.ref_func ops compiler state a b 0#u128 reachable
  | refIsNull => exact runtime.compiler.lower.FunctionCompiler.op.ref_is_null ops compiler state a b 0#u128 reachable
  | tableGet _ => exact runtime.compiler.lower.FunctionCompiler.op.table_get ops compiler state a b 0#u128 reachable
  | tableSet _ => exact runtime.compiler.lower.FunctionCompiler.op.table_set ops compiler state a b 0#u128 reachable
  | tableSize _ => exact runtime.compiler.lower.FunctionCompiler.op.table_size ops compiler state a b 0#u128 reachable
  | tableGrow _ => exact runtime.compiler.lower.FunctionCompiler.op.table_grow ops compiler state a b 0#u128 reachable
  | tableFill _ => exact runtime.compiler.lower.FunctionCompiler.op.table_fill ops compiler state a b 0#u128 reachable
  | tableCopy _ _ => exact runtime.compiler.lower.FunctionCompiler.op.table_copy ops compiler state a b 0#u128 reachable
  | tableInit _ _ => exact runtime.compiler.lower.FunctionCompiler.op.table_init ops compiler state a b 0#u128 reachable
  | elemDrop _ => exact runtime.compiler.lower.FunctionCompiler.op.elem_drop ops compiler state a b 0#u128 reachable
  | memorySize => exact runtime.compiler.lower.FunctionCompiler.op.memory_size ops compiler state a b 0#u128 reachable
  | memoryGrow => exact runtime.compiler.lower.FunctionCompiler.op.memory_grow ops compiler state a b 0#u128 reachable
  | memoryFill => exact runtime.compiler.lower.FunctionCompiler.op.memory_fill ops compiler state a b 0#u128 reachable
  | memoryCopy => exact runtime.compiler.lower.FunctionCompiler.op.memory_copy ops compiler state a b 0#u128 reachable
  | memoryInit _ => exact runtime.compiler.lower.FunctionCompiler.op.memory_init ops compiler state a b 0#u128 reachable
  | dataDrop _ => exact runtime.compiler.lower.FunctionCompiler.op.data_drop ops compiler state a b 0#u128 reachable

/-- Actual non-pair dispatch, with operand reads exposed for layout proofs. -/
theorem lower_stateful_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (first second a b entry : U32)
    (reachable : compiler.reachable = true) (single : statefulUsesPair op = false)
    (reads : StatefulReads ops compiler op first second) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (statefulInstruction op first second a entry) := by
  rw [lower_stateful_dispatch ops compiler state op a b reachable]
  obtain ⟨firstRead, secondRead⟩ := reads
  cases op <;> simp only [statefulUsesPair, Bool.true_eq_false] at single
  all_goals simp [SourceMachine.Stateful.Instruction.arity, statefulDepth] at firstRead
  all_goals simp only [statefulLowering, statefulInstruction]
  all_goals first
    | subst first; rfl
    | simp only [firstRead, secondRead _ rfl, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    | simp only [firstRead, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]

/-- The two pair-based callbacks resolve their exact newly appended entry
before reading the three scalar operands. -/
theorem lower_stateful_pair_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler paired : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (first second a b entry : U32)
    (reachable : compiler.reachable = true) (pairOpcode : statefulUsesPair op = true)
    (pair : runtime.compiler.FunctionCompiler.pair ops compiler a b = .ok (.Ok entry, paired))
    (read : runtime.compiler.FunctionCompiler.operand ops paired 3#usize = .ok (.Ok first)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops paired state
        (statefulInstruction op first second a entry) := by
  rw [lower_stateful_dispatch ops compiler state op a b reachable]
  cases op <;> simp only [statefulUsesPair, Bool.false_eq_true] at pairOpcode
  all_goals simp only [statefulLowering, statefulInstruction, pair, read, bind_ok, uncurry_apply_pair,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Runtime.Compiler

end

/-! ## StatefulSuccess -/

section

/-!
Acceptance of either pair-based callback exposes its actual allocation.

Main declarations: `lower_stateful_pair_success` and `compiler_finish_indirect`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallLowering`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Acceptance of either pair-based callback exposes its actual allocation. -/
theorem lower_stateful_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (reachable : before.reachable = true) (pairOpcode : statefulUsesPair op = true)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (), after)) :
    ∃ entry paired, runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok entry, paired) := by
  rw [lower_stateful_dispatch ops before state op a b reachable] at accepted
  cases op <;> simp only [statefulUsesPair, Bool.false_eq_true] at pairOpcode
  all_goals
    simp only [statefulLowering] at accepted
    obtain ⟨⟨result,paired⟩,pair,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok entry => exact ⟨entry,paired,pair⟩

/-- Finishing an ordinary instruction preserves the immutable pair table. -/
theorem compiler_finish_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (), after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) accepted).success
  have frame := compiler_observe_frame ops law middle state
  rw [rest,WP.spec_ok] at frame
  change ObserveFrame middle after at frame
  have same : after.function.indirect = middle.function.indirect := by rw [frame]
  obtain ⟨budget,code,sources,rfl,_,_⟩ := compiler_emit_success ops law before middle instruction emitted
  exact same

end Itasca.Runtime.Compiler

end
