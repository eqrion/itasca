import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ClosingContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Handler.ScalarCompleteness
import Itasca.Body.Control.EnterSound

/-!
Proofs for Runtime / Compiler / Local / Relations / Control.

This module collects ControlObservedLayout, KnownControlStack.
Each section documents its contracts and consumers.
-/

/-! ## ControlObservedLayout -/

section

open Itasca.Representation

/-! ## BranchReachable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

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
    CompilerLayout after (Itasca.Body.Stack.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth view (.Ok ()) accepted).observation
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Compiler

end

/-! ## ControlMapCounts -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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
end Itasca.Compiler

end

/-! ## BranchSuccessControls -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
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

end Itasca.Compiler

end

/-! ## ControlEntrySuccess -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## ControlObservation -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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

end Itasca.Compiler

end

/-! ## ControlObservedLayout -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem compiler_enter_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Body.Stack.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_enter_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

theorem compiler_end_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Body.Stack.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_end_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

theorem compiler_else_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Body.Stack.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_else_observation ops before after state bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Compiler

end

end

/-! ## KnownControlStack -/

section

/-!
# Concrete stacks after control changes

Closing or switching frames reconstructs concrete operands from saved outer values and the resolved signature, including after polymorphic unreachable arms.
-/
namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca

theorem concrete_values (types : List wasm_types.ValueType) : ConcreteStack (types.map code.StackType.Val) := by
  simp [ConcreteStack]

/-- Closing or switching a frame reconstructs a concrete stack from the saved
outer operands and its resolved signature, even after a polymorphic dead arm. -/
theorem concrete_end_effect {st out : code.BodyState} {parents blocks frame isElse inputs outputs outer}
    (known : ConcreteStack outer)
    (effect : Body.EndEffect st out parents blocks frame isElse inputs outputs outer) :
    ConcreteStack out.core.vals.val := by
  obtain ⟨_, effect⟩ := effect
  cases isElse with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at effect
    rw [effect.2.2]
    split
    · exact known
    · exact concrete_stack_append.mpr ⟨known, concrete_values outputs⟩
  | true =>
    simp only [↓reduceIte] at effect
    rw [effect.2.2]
    exact concrete_stack_append.mpr ⟨known, concrete_values inputs⟩

theorem end_concrete (st out : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType) (frame : code.Ctrl)
    (bt : signature.BlockType) (inputs outputs : List wasm_types.ValueType) (outer segment : List code.StackType)
    (controls : st.core.ctrls.val = parents ++ [frame]) (signatures : st.blocks.val = blocks ++ [bt])
    (aligned : blocks.length = parents.length) (values : st.core.vals.val = outer ++ segment)
    (base : frame.value_stack_base.val = outer.length)
    (inputTypes : Body.resolve env (Body.inputs bt) = some inputs)
    (outputTypes : Body.resolve env (Body.outputs bt) = some outputs)
    (shape : Body.Control.Shape st.core) (known : ConcreteStack outer)
    (accepted : code.end_frame st env isElse = .ok (.Ok (), out)) : ConcreteStack out.core.vals.val := by
  have effect := code.end_frame.sound st env isElse parents blocks frame bt inputs outputs outer segment
    controls signatures aligned values base inputTypes outputTypes shape
  rw [accepted, WP.spec_ok] at effect
  exact concrete_end_effect known (effect rfl).2.2

end Itasca.Compiler

end
