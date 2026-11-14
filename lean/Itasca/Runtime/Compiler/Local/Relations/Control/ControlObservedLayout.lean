import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf

/-!
Sections, each formerly its own module: BranchReachable, ControlMapCounts, BranchSuccessControls, ControlEntrySuccess, ControlObservation, ControlObservedLayout.
-/

/-! ## BranchReachable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096




theorem compiler_branch_reachable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.reachable = before.reachable := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).frame
  rw [frame]

theorem callback_branch_if_reachable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (view : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (status, after)) :
    after.reachable = before.reachable := by
  clear law
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth view status accepted with
  | dead dead observed => rw [compiler_observe_frame_raw ops _ _ _ _ observed]
  | rejected live branched =>
    rw [(runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branched).frame]
  | branched live branched observed =>
    rw [compiler_observe_frame_raw ops _ _ _ _ observed,
      (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branched).frame]
    rfl

theorem callback_branch_if_layout {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (view : Itasca.signature.ResultType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth view (.Ok ()) accepted).observation
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Runtime.Compiler

end

/-! ## ControlMapCounts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096



theorem compiler_end_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  exact (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind bt status accepted).map_count

theorem compiler_else_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv
    ops before after state bt status accepted
  have frame := effect.frame
  change after = _ at frame
  rw [frame]
end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessControls -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Branch emission only changes instructions, frame fixups and operand metadata;
it never changes the structural control map, including on a normal rejection. -/
theorem compiler_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).frame
  rw [frame]

theorem callback_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth ty status accepted).frame]

theorem callback_branch_if_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth ty status accepted).frame]

end Itasca.Runtime.Compiler

end

/-! ## ControlEntrySuccess -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Successful entry computes its exact slot and byte coordinates before any
allocation. These bounds follow from the actual checked model's normal return,
so dormant entries need no speculative source-stack size premise. -/
theorem control_entry_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (success : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    before.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max := by
  obtain ⟨priorFound, ctrlFound, signature, height, startPc, condition, source, middle,
    controlsFound, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind bt (.Ok ()) success).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have exactHeight := control_stack_height_success state.vals.deref ctrl.value_stack_base
    before.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  constructor
  · have bounded := height.hmax
    simp only [alloc.vec.Vec.deref, Slice.from_val] at exactHeight
    scalar_tac
  · have bounded := source.hmax
    scalar_tac


end Itasca.Runtime.Compiler

end

/-! ## ControlObservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096



/-- Successful control entry ends by observing the actual post-reader stack. -/
theorem compiler_enter_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind bt (.Ok ()) accepted).2.2 rfl
  exact ⟨middle, observed⟩


theorem compiler_end_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  exact (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind bt (.Ok ()) accepted).observation

theorem compiler_else_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  exact (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state bt (.Ok ()) accepted).observation

end Itasca.Runtime.Compiler

end

/-! ## ControlObservedLayout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


theorem compiler_enter_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_enter_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_end_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_end_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_else_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_else_observation ops before after state bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Runtime.Compiler

end
