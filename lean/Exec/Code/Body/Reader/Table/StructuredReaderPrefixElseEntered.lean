import Exec.Code.Local.Callbacks.Control.ElseSuccess
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixElseDormant
import Exec.Code.Local.Relations.Control.ControlObservedLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_callback_else_entered_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (state : code.OpIterState) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32) (form : current.form = .then_ sourceType condition)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (sourceTypes : SourceStack state.vals.val current.input)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ∃ noEntry : U32, noEntry.val = before.function.code.val.length + (if before.reachable then 1 else 0) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (current.begin_else sourceType condition before.function.code.val.length noEntry before.reachable)
        state.vals.val state.pos.val := by
  obtain ⟨prior, frame, framesEq, _, shape⟩ := invariant.frames.split
  have guardPosition : frame.if_pc.map UScalar.val = some current.entry := by
    simpa [SourceScope.guardPosition, form, entered] using shape.guard
  obtain ⟨guard, guardEq, guardAt⟩ : ∃ guard, frame.if_pc = some guard ∧ guard.val = current.entry := by
    cases hasGuard : frame.if_pc with
    | none => simp [hasGuard] at guardPosition
    | some guard => exact ⟨guard, rfl, by simpa [hasGuard] using guardPosition⟩
  have guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
    have retained : current.entered = true → before.function.code.val[current.entry]? = some (.JumpIfZero condition core.num.U32.MAX) := by
      simpa [ScopeEntryCode, form] using shape.entryCode
    simpa [guardAt] using retained entered
  have entryReachable := shape.entered.trans entered
  have bound := invariant.codeBudget.fetch_bound sourceBound
  obtain ⟨noEntry, fixups, live, change⟩ : ∃ noEntry fixups,
      after.reachable = true ∧ ElseTransition before after prior frame guard
        (alloc.vec.Vec.len before.function.code) condition core.num.U32.MAX noEntry fixups before.reachable := by
    cases reachable : before.reachable with
    | false =>
      let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
      have targetAt : target.val = before.function.code.val.length := rfl
      have effect := compiler_else_dead ops law before state bt frame prior guard condition target
        framesEq reachable guardEq guardCode targetAt
      rw [accepted, WP.spec_ok] at effect
      obtain ⟨live, code, frames⟩ := effect rfl
      dsimp only at live code frames
      refine ⟨target, frame.fixups, live.trans entryReachable, ?_⟩
      exact ⟨framesEq, by simpa using frames, guardCode, rfl, by simpa using targetAt,
        by simp, by simpa using code⟩
    | true =>
      let target : U32 := UScalar.ofNatCore (before.function.code.val.length + 1) (by scalar_tac)
      have targetAt : target.val = before.function.code.val.length + 1 := rfl
      obtain ⟨live, code, fixups, appended, frames⟩ := compiler_else_live_success ops law before after state bt
        frame prior guard condition target framesEq reachable guardEq guardCode targetAt accepted
      refine ⟨target, fixups, live.trans entryReachable, ?_⟩
      exact ⟨framesEq, by simpa using frames, guardCode, rfl, by simpa using targetAt,
        by simpa using appended, by simpa using code⟩
  have stable := compiler_else_stable_result ops law before after state bt (.Ok ()) accepted
  have maps := compiler_else_map_count ops law before after state bt (.Ok ()) accepted
  have sources := compiler_else_sources ops law before after state bt accepted
  have cursor := compiler_else_cursor ops law before after state bt accepted
  have localsAfter := (invariant.metadata.trans stable).local_layout initialLocals
  have layout : CompilerLayout after current.input := by
    simpa only [sourceTypes.decoded] using compiler_else_layout_success ops law before after state bt sourceTypes.concrete localsAfter accepted
  exact ⟨noEntry, change.noPosition, invariant.begin_else entered live stack stable maps prior frame guard
    (alloc.vec.Vec.len before.function.code) condition core.num.U32.MAX noEntry fixups change sourceType form guardEq
    layout sourceTypes sources consumed (by rw [cursor])⟩
end Exec.Code
