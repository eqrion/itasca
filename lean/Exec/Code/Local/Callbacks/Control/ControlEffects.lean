import Exec.Code.Local.Callbacks.Common.OrdinaryEffects
import Exec.Code.Local.Callbacks.Calls.CallbackCapacity
import Exec.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Exec.Code.Local.Callbacks.Calls.FixupCallbacks
import Exec.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Exec.Code.Local.Callbacks.Control.FixupElsePreservation
import Exec.Code.Local.Callbacks.Table.CallbackTables
import Exec.Code.Local.Callbacks.Table.CompilerTableScratchCallbacks
import Exec.Code.Local.Callbacks.Table.CompilerTableScratchControl
import Exec.Code.Local.Capacity.ControlCapacity
import Exec.Code.Local.Relations.Table.ControlTablePreservation

/-!
What every structured-control compiler callback preserves: the function
tables, the branch-table depths, emitted code, the fixup budget, and slot
capacity.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

structure ControlEffects {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) : Prop where
  tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function
  depths : after.table_depths = before.table_depths
  code_mono : before.function.code.val.length ≤ after.function.code.val.length
  fixups : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length
  capacity : CapacityStep before after state

theorem ControlEffects.auxiliary_growth {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} (effects : ControlEffects before after state) :
    AuxiliaryGrowth before after :=
  .of_tables effects.tables effects.code_mono

theorem compiler_block_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_block_tables ops law before after state bt accepted,
    compiler_block_depths ops law before after state bt accepted,
    compiler_block_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Block bt budget accepted,
    compiler_block_capacity ops law before after state bt accepted⟩

theorem compiler_loop_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_loop_tables ops law before after state bt accepted,
    compiler_loop_depths ops law before after state bt accepted,
    compiler_loop_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Loop bt budget accepted,
    compiler_loop_capacity ops law before after state bt accepted⟩

theorem compiler_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_if_tables ops law before after state bt accepted,
    compiler_if_depths ops law before after state bt accepted,
    compiler_if_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Then bt budget accepted,
    compiler_if_capacity ops law before after state bt accepted⟩

theorem compiler_else_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_else_tables ops law before after state bt accepted,
    compiler_else_depths ops law before after state bt accepted,
    compiler_else_code_mono ops law before after state bt accepted,
    fun budget => compiler_else_fixup_budget ops law before after state bt budget accepted,
    compiler_else_capacity ops law before after state bt accepted⟩

theorem compiler_end_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_end_tables ops law before after state kind bt accepted,
    compiler_end_depths ops law before after state kind bt accepted,
    compiler_end_code_mono ops law before after state kind bt accepted,
    fun budget => compiler_end_fixup_budget ops law before after state kind bt budget accepted,
    compiler_end_capacity ops law before after state kind bt accepted⟩

theorem compiler_br_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_br_tables ops law before after state depth types accepted,
    compiler_br_depths ops law before after state depth types accepted,
    compiler_br_code_mono ops law before after state depth types accepted,
    fun budget => compiler_br_fixup_budget ops law before after state depth types budget accepted,
    compiler_br_capacity ops law before after state depth types accepted⟩

theorem compiler_br_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_br_if_tables ops law before after state depth types accepted,
    compiler_br_if_depths ops law before after state depth types accepted,
    compiler_br_if_code_mono ops law before after state depth types accepted,
    fun budget => compiler_br_if_fixup_budget ops law before after state depth types budget accepted,
    compiler_br_if_capacity ops law before after state depth types accepted⟩

end Itasca.Runtime.Code
