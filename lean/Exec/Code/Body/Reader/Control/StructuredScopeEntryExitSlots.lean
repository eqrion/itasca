import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables
import Exec.Code.Local.Relations.Control.ControlEntrySuccess
import Exec.Code.Local.Checking.ScopeEntryExitSlots

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source-selected control signatures and live IF layouts establish actual
scope-entry recorded exit-slot bounds, including dormant entries. -/
theorem structured_scope_entry_exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (kind : code.LabelKind) (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (allowed : kind = .Block ∨ kind = .Loop ∨ kind = .Then)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt before.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (ifLayout : kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]))
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨heightFits,sourceFits⟩ := control_entry_coordinates ops before after state ctrl prior kind bt controls valuesFit called
  obtain ⟨codeFits,offsetsFit,mapsFit,framesFit⟩ := invariant.capacities sourceBound
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let makeGeometry (pc : U32) : ScopeEntryGeometry before state bt :=
    ⟨ctrl,prior,signature,pc,controls,selected,valuesFit,heightFits,sourceFits,mapsFit,framesFit⟩
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  by_cases live : before.reachable = true
  · rcases allowed with rfl | rfl | rfl
    · exact compiler_scope_entry_exit_slots ops law before after state .Block bt (makeGeometry pc)
        (.block live rfl) held called
    · exact compiler_scope_entry_exit_slots ops law before after state .Loop bt (makeGeometry pc)
        (.loop live rfl codeFits offsetsFit) held called
    · obtain ⟨stack,layout⟩ := ifLayout rfl live
      let guardedPc : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
      exact compiler_scope_entry_exit_slots ops law before after state .Then bt (makeGeometry guardedPc)
        (.if_ stack layout live rfl codeFits offsetsFit) held called
  · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
    exact compiler_scope_entry_exit_slots ops law before after state kind bt (makeGeometry pc)
      (.dead kind dead rfl) held called

end Exec.Code
