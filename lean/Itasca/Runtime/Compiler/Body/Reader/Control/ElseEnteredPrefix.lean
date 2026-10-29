import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Compiler.Body.Reader.Control.ElseDormantPrefix
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts

/-!
Structured elseentered reader prefixes and their complete-profile transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix Else Entered -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Else Entered Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_else_entered_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0x05#u8 before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Wasm2.blockType p.current.bt) condition ∧
      noEntry.val = before.function.code.val.length + (if before.reachable then 1 else 0) ∧
      let next := current.begin_else (Wasm2.blockType p.current.bt) condition before.function.code.val.length noEntry before.reachable
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals parents next out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 parents next p.parents p.current.nextElse ∧
      ReaderReachabilityWasm2 after.reachable parents next p.parents p.current.nextElse ∧
      ReaderScopeFronts parents next (p.parents.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out p.parents p.current.nextElse ∧ p.After out := by
  obtain ⟨callback, read, sourceForm, encoded, results, opened, afterState⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition, rfl⟩
  obtain ⟨condition, form⟩ := sourceThen
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have outerKnown : ConcreteStack outer := by
    rw [wasm2_spine_values spine]
    simpa only [List.flatMap_def] using savedKnown.current entered
  have erased : code.end_frame st env true = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  have known := wasm2_end_concrete st out env true (p.parents.map Wasm2.Frames.Saved.ctrl)
    (p.parents.map Wasm2.Frames.Saved.bt) p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core outerKnown erased
  have frontEq : current.front = Sequence.stackTypes outer := by
    rw [wasm2_spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ invariant.known live)).2
    have mono := reach.current live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceTypes : SourceStack out.core.vals.val current.input := by
    refine ⟨known, ?_⟩
    obtain ⟨C', outer', spine', header', base', typed', controls', blocks', values'⟩ := opened
    have outerTypes : Sequence.stackTypes outer' = current.front := by
      rw [wasm2_spine_values spine']
      simpa only [List.flatMap_def] using fronts.current.symm
    simp only [values', Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer' ++ Sequence.stackTypes p.current.nextElse.vals = current.input
    rw [outerTypes]
    have params := same.current.params
    rw [sourceForm] at params
    simp only [Wasm2.Frames.Form.params] at params
    simp [Wasm2.Frames.Saved.nextElse, SourceScope.input, params, Sequence.stackTypes, List.map_map, Function.comp_def]
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  obtain ⟨noEntry, positionEq, certified⟩ := structured_callback_else_entered_prefix ops law initial before after types functions returns compilerLocals
    parents current st.core.vals.val p.start.val invariant initialLocals entered out.core p.current.bt
    (Wasm2.blockType p.current.bt) condition form stack sourceTypes sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form before.function.code.val.length noEntry before.reachable,
    reach.begin_else after.reachable _ condition before.function.code.val.length noEntry before.reachable,
    fronts.begin_else _ condition before.function.code.val.length noEntry before.reachable,
    reader_else_boundary_wasm2 p sourceForm encoded opened afterState, afterState⟩
end Itasca.Runtime.Compiler

end
