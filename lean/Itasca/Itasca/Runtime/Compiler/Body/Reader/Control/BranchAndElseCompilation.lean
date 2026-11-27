import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Body.Trace.BytesDispatch
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Runtime.Compiler.Local.Control.Structured.NestedScopes
import Itasca.Runtime.Compiler.Local.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Body.Relations.Table.BranchTableTables
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Body.Reader.StackValues

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects BranchAndElseCompilation, BranchTableCapacity, BranchTableIndexed, RootCompilation.
Each section documents its contracts and consumers.
-/

/-! ## BranchAndElseCompilation -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects ElseCompilation, BranchesCompilation.
Each section documents its contracts and consumers.
-/

/-! ## ElseCompilation -/

section

open Itasca.Representation

/-! ## ElseDormantPrefix -/

section

/-!
An actual ELSE in an omitted IF changes only its retained source arm and physical frame kind. No emitted-code relation is assumed for the omitted arm.

Main declarations: `structured_callback_else_dormant_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual ELSE in an omitted IF changes only its retained source arm and
physical frame kind. No emitted-code relation is assumed for the omitted arm. -/
theorem structured_callback_else_dormant_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (unentered : current.entered = false)
    (state : code.OpIterState) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32) (form : current.form = .then_ sourceType condition)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ∃ noEntry : U32, noEntry.val = before.function.code.val.length ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (current.begin_else sourceType condition noEntry.val noEntry false) state.vals.val state.pos.val := by
  have dead : before.reachable = false := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal dead _ _ => exact dead
    | dormant dead _ => exact dead
  obtain ⟨prior, frame, framesEq, _, shape⟩ := invariant.frames.split
  have noGuard : frame.if_pc = none := by
    simpa [SourceScope.guardPosition, form, unentered] using shape.guard
  have effect := compiler_else_unentered ops law before state bt frame prior framesEq dead noGuard
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨reach, codeEq, afterFrames⟩ := effect rfl
  dsimp only at reach codeEq afterFrames
  have deadAfter : after.reachable = false := reach.trans (shape.entered.trans unentered)
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let noEntry : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : noEntry.val = before.function.code.val.length := rfl
  have stable := compiler_else_stable_result ops law before after state bt (.Ok ()) accepted
  have maps := compiler_else_map_count ops law before after state bt (.Ok ()) accepted
  have sources := compiler_else_sources ops law before after state bt accepted
  have cursor := compiler_else_cursor ops law before after state bt accepted
  exact ⟨noEntry, positionEq, invariant.begin_else_dormant unentered deadAfter stable maps prior frame
    framesEq afterFrames codeEq sourceType condition noEntry form positionEq sources consumed (by rw [cursor])⟩
end Itasca.Compiler

end

/-! ## ElseDormantPrefix -/

section

/-!
Complete-source-prefix transport of a dormant else prefix.

Main declarations: `structured_reader_prefix_else_dormant`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_else_dormant {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (unentered : current.entered = false)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x05#u8 before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Body.blockType p.current.bt) condition ∧
      noEntry.val = before.function.code.val.length ∧
      let next := current.begin_else (Body.blockType p.current.bt) condition noEntry.val noEntry false
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals parents next out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper parents next p.parents p.current.nextElse ∧
      BodyReaderReachability after.reachable parents next p.parents p.current.nextElse ∧
      ReaderScopeFronts parents next (p.parents.map Body.Frames.Saved.vals) ∧
      ReaderBoundary data env locals index p.ft out p.parents p.current.nextElse ∧ p.After out := by
  obtain ⟨callback, read, sourceForm, encoded, results, opened, afterState⟩ := reader_else p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Body.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition, rfl⟩
  obtain ⟨condition, form⟩ := sourceThen
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
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
  obtain ⟨noEntry, positionEq, certified⟩ := structured_callback_else_dormant_prefix ops law initial before after types functions returns compilerLocals
    parents current st.core.vals.val p.start.val invariant unentered out.core p.current.bt
    (Body.blockType p.current.bt) condition form sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form noEntry.val noEntry false,
    reach.begin_else after.reachable _ condition noEntry.val noEntry false,
    fronts.begin_else _ condition noEntry.val noEntry false,
    reader_else_boundary p sourceForm encoded opened afterState, afterState⟩
end Itasca.Compiler

end

/-! ## ElseEnteredPrefix -/

section

/-!
Structured elseentered reader prefixes and their complete transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix Else Entered -/

section

namespace Itasca.Compiler
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
    (stack : before.reachable = true → Body.Stack.stackTypes raw = current.front ++ current.results)
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
end Itasca.Compiler

end

/-! ## Structured Reader Prefix Else Entered Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem structured_reader_prefix_else_entered {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x05#u8 before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Body.blockType p.current.bt) condition ∧
      noEntry.val = before.function.code.val.length + (if before.reachable then 1 else 0) ∧
      let next := current.begin_else (Body.blockType p.current.bt) condition before.function.code.val.length noEntry before.reachable
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals parents next out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipper parents next p.parents p.current.nextElse ∧
      BodyReaderReachability after.reachable parents next p.parents p.current.nextElse ∧
      ReaderScopeFronts parents next (p.parents.map Body.Frames.Saved.vals) ∧
      ReaderBoundary data env locals index p.ft out p.parents p.current.nextElse ∧ p.After out := by
  obtain ⟨callback, read, sourceForm, encoded, results, opened, afterState⟩ := reader_else p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Body.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition, rfl⟩
  obtain ⟨condition, form⟩ := sourceThen
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have outerKnown : ConcreteStack outer := by
    rw [spine_values spine]
    simpa only [List.flatMap_def] using savedKnown.current entered
  have erased : code.end_frame st env true = .ok (.Ok (), out) := by
    simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
  have known := end_concrete st out env true (p.parents.map Body.Frames.Saved.ctrl)
    (p.parents.map Body.Frames.Saved.bt) p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core outerKnown erased
  have frontEq : current.front = Body.Stack.stackTypes outer := by
    rw [spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Body.Stack.stackTypes st.core.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ invariant.known live)).2
    have mono := reach.current live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Body.Stack.stackTypes, List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceTypes : SourceStack out.core.vals.val current.input := by
    refine ⟨known, ?_⟩
    obtain ⟨C', outer', spine', header', base', typed', controls', blocks', values'⟩ := opened
    have outerTypes : Body.Stack.stackTypes outer' = current.front := by
      rw [spine_values spine']
      simpa only [List.flatMap_def] using fronts.current.symm
    simp only [values', Body.Stack.stackTypes, List.map_append]
    change Body.Stack.stackTypes outer' ++ Body.Stack.stackTypes p.current.nextElse.vals = current.input
    rw [outerTypes]
    have params := same.current.params
    rw [sourceForm] at params
    simp only [Body.Frames.Form.params] at params
    simp [Body.Frames.Saved.nextElse, SourceScope.input, params, Body.Stack.stackTypes, List.map_map, Function.comp_def]
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
    (Body.blockType p.current.bt) condition form stack sourceTypes sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form before.function.code.val.length noEntry before.reachable,
    reach.begin_else after.reachable _ condition before.function.code.val.length noEntry before.reachable,
    fronts.begin_else _ condition before.function.code.val.length noEntry before.reachable,
    reader_else_boundary p sourceForm encoded opened afterState, afterState⟩
end Itasca.Compiler

end

end

/-! ## ElseCompilation -/

section

/-!
Else-entry compilation through a structured reader state.

Main declarations: `StructuredReaderCompilerState.begin_else` and `StructuredReaderCompilerState.else_`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.begin_else {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.begin_else (Body.blockType savedCurrent.bt) condition before.function.code.val.length noEntry before.reachable)
      savedParents savedCurrent.nextElse := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_else_entered p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    exact ⟨condition, noEntry, compiled, boundary, same, reach, fronts, state.knownFronts.begin_else _ condition _ noEntry _⟩
  | false =>
    have dead : before.reachable = false := by
      cases state.compiled.mode with
      | live _ live _ => simp [entered] at live
      | terminal dead _ _ => exact dead
      | dormant dead _ => exact dead
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_else_dormant p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    refine ⟨condition, noEntry, ?_⟩
    simpa only [dead, positionEq] using
      (⟨compiled, boundary, same, reach, fronts, state.knownFronts.begin_else _ condition _ noEntry _⟩ : StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
        parents (current.begin_else (Body.blockType savedCurrent.bt) condition noEntry.val noEntry false)
        savedParents savedCurrent.nextElse)
theorem StructuredReaderCompilerState.else_ {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_ELSE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨condition, noEntry, nextState⟩ := state.begin_else ops law initialLocals next advance inbounds out byte accepted
  exact nextState.point

end Itasca.Compiler

end

end

/-! ## BranchesCompilation -/

section

open Itasca.Representation

/-! ## StructuredBranchLayout -/

section

/-!
Exact live branch slot coordinates follow from source scope selection and the compiler's current layout; no equality of word widths substitutes for a target's source type list.

Main declarations: `StructuredCompilerPrefix.branch_layout`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Exact live branch slot coordinates follow from source scope selection and
the compiler's current layout; no equality of word widths substitutes for a
target's source type list. -/
theorem StructuredCompilerPrefix.branch_layout {jumpTables : List Aeneas.Std.U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Body.Stack.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes = before.height.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate
    (input ▸ retained.layout) retained.localsEq
  exact ⟨index, frame, source, found, position, shape, height, sourcePosition, sourceWidth⟩

end Itasca.Compiler

end

/-! ## BranchesCompilation -/

section

/-!
Direct and conditional branch prefixes and structured compilation. Live/dormant prefix transitions compose into the reader-state branch results.
-/

/-! ## Structured Compiler Prefix Br -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The accepted callback realizes the selected source branch, for both forward
fixups and loop backedges. All instruction coordinates follow from the prefix. -/
theorem StructuredCompilerPrefix.br_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (reachable : before.reachable = true) (depth : U32) (view : signature.ResultType)
    (scope : SourceScope) (selected : (current :: parents.reverse)[depth.val]? = some scope)
    (discarded : List valtype)
    (input : Body.Stack.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = false := by
  classical
  obtain ⟨index, frame, source, found, position, shape, destination, sourcePosition, sourceWidth⟩ :=
    invariant.branch_layout reachable depth.val scope selected discarded input
  have stable := compiler_br_stable_result ops law before after state depth view (.Ok ()) accepted
  have maps := callback_branch_controls_result ops law before after state depth view (.Ok ()) accepted
  have sources := compiler_br_sources ops law before after state depth view accepted
  have cursor := compiler_br_cursor ops law before after state depth view accepted
  by_cases isLoop : frame.kind = .Loop
  · have width : frame.params.val = slots scope.branchTypes := by simpa only [isLoop] using shape.toScopeFrameShape.branch_width
    obtain ⟨dead, code, frames⟩ := callback_branch_loop_success ops law before state view reachable frame index depth source found
      position isLoop (by simpa only [width] using sourceWidth) after accepted
    have ordinary : CompilerOrdinaryStable before after :=
      ⟨by simp only [compilerOrdinaryMetadata, stable.metadata, frames, maps], stable.capacity⟩
    refine ⟨?_, dead⟩
    exact invariant.branch_loop reachable dead ordinary frame index.val depth.val scope frame.height source frame.params
      found isLoop position selected discarded input destination sourcePosition width code sources consumed (by rw [cursor])
  · have width : frame.results.val = slots scope.branchTypes := by
      have width := shape.toScopeFrameShape.branch_width
      cases kind : frame.kind <;> simp_all
    obtain ⟨dead, fixups, frames, _, code, site, sitePosition, appended⟩ :=
      callback_branch_forward_success ops law before state view reachable frame index depth source found position isLoop
        (by simpa only [width] using sourceWidth) after accepted
    refine ⟨?_, dead⟩
    exact invariant.branch_forward reachable dead stable maps frame index.val depth.val scope frame.height source frame.results
      core.num.U32.MAX site fixups found isLoop position selected discarded input destination sourcePosition width sitePosition
      appended code frames sources consumed (by rw [cursor])

theorem StructuredCompilerPrefix.br_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false) (depth : U32) (view : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = false := by
  have sources := compiler_br_sources ops law before after state depth view accepted
  have cursor := compiler_br_cursor ops law before after state depth view accepted
  have accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after) := by
    have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv
      ops before after state depth view (.Ok ()) accepted
    cases effect with
    | dead _ observed => exact observed
    | branched live _ _ => simp [dead] at live
  have ordinary := compiler_observe_ordinary_stable ops law before after state accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have deadAfter : after.reachable = false := by rw [frame]; exact dead
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip _ dead deadAfter ordinary code sources consumed (by rw [cursor]), deadAfter⟩
end Itasca.Compiler

end

/-! ## Structured Compiler Prefix Br If -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.br_if_live {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (known : ConcreteStack state.vals.val) (consumed : position < state.pos.val)
    (reachable : before.reachable = true) (depth : U32) (view : signature.ResultType)
    (scope : SourceScope) (selected : (current :: parents.reverse)[depth.val]? = some scope)
    (discarded : List valtype)
    (input : Body.Stack.stackTypes raw = Body.Stack.stackTypes state.vals.val ++ [.I32])
    (targetStack : Body.Stack.stackTypes state.vals.val = scope.front ++ discarded ++ scope.branchTypes)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = before.reachable := by
  classical
  obtain ⟨_, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, source, condition, found, position, shape, destination, sourcePosition, sourceWidth, conditionAt, conditionSlot⟩ :=
    invariant.branch_if_coordinates reachable depth.val scope selected discarded input targetStack
  have stable := compiler_br_if_stable_result ops law before after state depth view (.Ok ()) accepted
  have maps := callback_branch_if_controls_result ops law before after state depth view (.Ok ()) accepted
  have sources := compiler_br_if_sources ops law before after state depth view accepted
  have cursor := compiler_br_if_cursor ops law before after state depth view accepted
  have reach := callback_branch_if_reachable_result ops law before after state depth view (.Ok ()) accepted
  have live : after.reachable = true := reach.trans reachable
  have localBefore : LocalLayout before := ⟨retained.layout.localSlots, retained.layout.localOffsets⟩
  have layout := callback_branch_if_layout ops law before after state depth view known (stable.local_layout localBefore) accepted
  refine ⟨?_, reach⟩
  by_cases isLoop : frame.kind = .Loop
  · have width : frame.params.val = slots scope.branchTypes := by simpa only [isLoop] using shape.toScopeFrameShape.branch_width
    obtain ⟨resume, resumePosition⟩ := invariant.codeBudget.branch_resume sourceBound frame.params source frame.height
    obtain ⟨code, frames⟩ := callback_branch_if_loop_success ops law before state view reachable frame index depth source condition resume
      found position isLoop (by simpa only [width] using sourceWidth) conditionAt resumePosition after accepted
    have ordinary : CompilerOrdinaryStable before after :=
      ⟨by simp only [compilerOrdinaryMetadata, stable.metadata, frames, maps], stable.capacity⟩
    have resumeEnd : resume.val = after.function.code.val.length := by
      rw [code, List.length_append, resumePosition]
      unfold branchIfInstructions
      split <;> simp
    exact invariant.branch_if_loop reachable live ordinary frame index.val depth.val scope frame.height source frame.params condition resume
      found isLoop position selected discarded input targetStack destination sourcePosition width code ⟨known, rfl⟩ layout
      conditionSlot resumeEnd sources consumed (by rw [cursor])
  · have width : frame.results.val = slots scope.branchTypes := by
      have width := shape.toScopeFrameShape.branch_width
      cases kind : frame.kind <;> simp_all
    obtain ⟨resume, resumePosition⟩ := invariant.codeBudget.branch_resume sourceBound frame.results source frame.height
    have fixupsBefore := (retained.sites frame (List.mem_of_getElem? found)).branches.inside
    obtain ⟨fixups, frames, _, code, site, sitePosition, appended⟩ :=
      callback_branch_if_forward_success ops law before state view reachable frame index depth source condition resume found position isLoop
        (by simpa only [width] using sourceWidth) conditionAt resumePosition fixupsBefore after accepted
    exact invariant.branch_if_forward reachable live stable maps frame index.val depth.val scope frame.height source frame.results
      core.num.U32.MAX condition resume site fixups found isLoop position selected discarded input targetStack destination sourcePosition width
      sitePosition appended code frames ⟨known, rfl⟩ layout conditionSlot resumePosition sources consumed (by rw [cursor])

theorem StructuredCompilerPrefix.br_if_dead {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState) (consumed : position < state.pos.val)
    (dead : before.reachable = false) (depth : U32) (view : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
      state.vals.val state.pos.val ∧ after.reachable = before.reachable := by
  have sources := compiler_br_if_sources ops law before after state depth view accepted
  have cursor := compiler_br_if_cursor ops law before after state depth view accepted
  have reach := callback_branch_if_reachable_result ops law before after state depth view (.Ok ()) accepted
  have accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after) := by
    have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv
      ops before after state depth view (.Ok ()) accepted
    cases effect with
    | dead _ observed => exact observed
    | branched live _ _ => simp [dead] at live
  have ordinary := compiler_observe_ordinary_stable ops law before after state accepted
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have code : after.function.code = before.function.code := by rw [frame]
  exact ⟨invariant.skip _ dead (reach.trans dead) ordinary code sources consumed (by rw [cursor]), reach⟩
end Itasca.Compiler

end

/-! ## Structured Reader Prefix Br -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, Body.ReaderPost p out.core (.BR (.mk_uN depth.val)) true [] ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨depth, view, callback, read, post⟩ := reader_br p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input⟩ := reader_br_layout p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_live ops law out.core consumed reachable depth view scope selected discarded input callback
  · exact invariant.br_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Br If -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br_if {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨depth, view, values, callback, read, post⟩ := reader_br_if p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, values, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input, targetStack, known⟩ := reader_br_if_layout p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_if_live ops law out.core known consumed reachable depth view scope selected discarded input targetStack
      ((Nat.le_of_lt p.inbounds).trans sourceBound) callback
  · exact invariant.br_if_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Branches -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.br {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (byte : data.val[st.core.pos.val]'inbounds = 12#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR (.mk_uN depth.val))) (.BR (.mk_uN depth.val)) true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, post, compiled, dead⟩ := structured_reader_prefix_br p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current byte accepted
  exact ⟨depth, state.advance next advance inbounds post
    (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerState.br_if {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[st.core.pos.val]'inbounds = 13#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType), StructuredReaderCompilerState jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR_IF (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR_IF (.mk_uN depth.val))) (.BR_IF (.mk_uN depth.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, values, post, compiled, reach⟩ := structured_reader_prefix_br_if p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current sourceBound byte accepted
  exact ⟨depth, values, state.advance next advance inbounds post
    (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reach.symm.trans live))⟩

end Itasca.Compiler

end

end

end

end

/-! ## BranchTableCapacity -/

section

/-!
Compiler capacity after reading a br_table label vector.

Main declarations: `reader_table_capacity`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x0e#u8 before=.ok (.Ok (),out,after)) : CapacityStep before after out.core := by
  rw [Body.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨count,first,selector,popped,depths,fallback,types,defaultStart,readState,budget,buffer,
    _,_,_,_,_,_,_,callback⟩ := compiler_read_br_table ops law before after st out data env accepted
  exact compiler_br_table_capacity ops law {before with budget,table_depths:=buffer} after out.core fallback types callback
end Itasca.Compiler

end

/-! ## BranchTableIndexed -/

section

/-!
Indexed br_table compilation from the decoded reader instruction through source prefixes and scratch tables. The final theorem retains the complete indexed compiler-table relation.
-/

/-! ## Structured Compiler Prefix Table -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual successful live table callback advances the indexed compiler
certificate once, retaining every dispatch arm under all future fixup plans. -/
theorem StructuredCompilerPrefix.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables : List U32} {emit types functions returns locals parents current raw position nextRaw}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (depths : List U32) (fallback : U32) (blockTypes : signature.ResultType)
    (stack : List valtype) (stackEq : Body.Stack.stackTypes raw = stack ++ [.I32])
    (inputs : TableOperandScopes (parents ++ [current]) stack (depths ++ [fallback]))
    (buffer : before.table_depths.val = depths)
    (dominance : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (futureTables : List U32) (tableEq : jumpTables = after.function.jump_tables.val ++ futureTables)
    (gate : ∀ selector start len, emit (stack ++ [.I32])
      (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))
      [.JumpTable selector start len] stack)
    (consumed : position + depths.length + 2 ≤ state.pos.val)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback blockTypes = .ok (.Ok (),after)) :
    StructuredCompilerPrefix jumpTables emit initial after types functions returns locals parents
      (current.advance (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))) nextRaw state.pos.val := by
  obtain ⟨entered, original⟩ := invariant.live live
  have retained : StructuredUniversalPrefix jumpTables emit before types functions returns locals
      parents current (stack ++ [.I32]) := stackEq ▸ original
  have fixed := compiler_br_table_fixed ops law before after state fallback blockTypes live accepted
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, fixed.stable.fields.2.2.2.2.1]
    exact retained.localsEq
  obtain ⟨frames, dormant, sites⟩ := compiler_br_table_scope_frames ops law before after state fallback blockTypes
    invariant.frames invariant.entryChain entered retained.sites (by rw [fixed.controls]) live accepted
  obtain ⟨sources, cursor⟩ := compiler_br_table_sources ops law before after state fallback blockTypes accepted
  obtain ⟨budget, collected, start, len, selector, emitted, lowered, targets,
    collectedEq, startEq, lenEq, emission, built, codeEq, framesEq, tableAppend, count, clear, dead, header⟩ :=
    compiler_br_table_production ops law before after state fallback blockTypes live accepted
  have framesLength : after.frames.val.length = before.frames.val.length := by
    rw [framesEq, built.frame_length]
    obtain ⟨_, _, _, emittedEq, _, _⟩ := emission
    rw [emittedEq]
  have completion : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
      ∃ previous selector start len suffix,
        FramePlans before.function.code.val.length locals before.frames.val (label :: labels) previous ∧
        resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ suffix ∧
        BranchTableLayout jumpTables locals (label :: labels) stack (resolvedCode after.function.code.val groups)
          (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
          before.function.code.val.length after.function.code.val.length selector start len ∧
        before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    intro label labels groups plans shape parentShapes
    have shapes : List.Forall₂ ScopeLabel (parents ++ [current]).reverse (label :: labels) := by
      simpa using List.Forall₂.cons shape parentShapes
    obtain ⟨previous, start, len, selector, previousPlans, table, header, _, _, extra, code⟩ :=
      compiler_br_table_layout_prefix ops law before after state fallback blockTypes locals stack
        (parents ++ [current]) (label :: labels) depths groups buffer retained.layout retained.localsEq
        (invariant.frames.frames.imp (fun _ _ p => p.toScopeFrameShape)) shapes inputs dominance retained.sites
        plans live accepted
    refine ⟨previous, selector, start, len, .JumpTable selector start len :: extra, previousPlans, code, ?_, header⟩
    simpa only [tableEq] using table.append_tables futureTables
  have terminal := retained.branch_table _ _ localsEq sites gate completion
  have arms := invariant.arms.resolved_append (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val))
    (by
      intro label labels groups plans shape parentShapes
      obtain ⟨previous, selector, start, len, suffix, previousPlans, code, _, _⟩ :=
        completion label labels groups plans shape parentShapes
      exact ⟨previous, suffix, previousPlans, code⟩)
  have growth := compiler_br_table_code_growth ops law before after state fallback blockTypes live accepted
  rw [buffer] at growth
  refine ⟨invariant.metadata.trans fixed.stable, frames.advance _, invariant.entryChain.advance _, dormant,
    invariant.conditions.advance _, (by intro contradiction; simp [dead] at contradiction),
    .terminal dead entered terminal, arms, sources.aligned invariant.sources, ?_, ?_, ?_⟩
  · exact invariant.codeBudget.table growth (by omega)
  · exact (invariant.controlBudget.transport (by rw [fixed.controls]) (Nat.le_of_eq framesLength)).advance (by omega)
  · rw [cursor]
end Itasca.Compiler

end

/-! ## Structured Table Scratch -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Collecting table labels changes only private scratch and allocation
accounting; it preserves the complete source/code invariant. -/
theorem StructuredCompilerPrefix.table_scratch {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (budget : runtime.compiler.Budget A) (depths : alloc.vec.Vec U32) :
    StructuredCompilerPrefix jumpTables emit initial {before with budget,table_depths := depths}
      types functions returns locals parents current raw position := by
  refine ⟨⟨invariant.metadata.metadata,invariant.metadata.capacity⟩,?_,invariant.entryChain,invariant.dormant,
    invariant.conditions,invariant.known,?_,invariant.arms,invariant.sources,invariant.codeBudget,
    ⟨invariant.controlBudget.maps,invariant.controlBudget.frames⟩,invariant.cursor⟩
  · refine ⟨invariant.frames.nested,?_⟩
    exact invariant.frames.frames.imp (fun _ _ frame =>
      ⟨frame.toScopeFrameShape,frame.mapBound,frame.entryBound,frame.bodyBound,frame.entryCode⟩)
  · cases invariant.mode with
    | live reachable entered retained =>
      exact .live reachable entered ⟨retained.localsEq,
        ⟨retained.layout.localSlots,retained.layout.localOffsets,retained.layout.operandOffsets,
          retained.layout.height,retained.layout.capacity⟩,retained.sites,retained.prefixes⟩
    | terminal reachable entered retained =>
      exact .terminal reachable entered ⟨retained.localsEq,retained.sites,retained.prefixes⟩
    | dormant reachable retained =>
      exact .dormant reachable ⟨retained.unentered,retained.localsEq,retained.sites,retained.prefixes⟩
end Itasca.Compiler

end

/-! ## Reader Table Decoded -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_table_decoded {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Body.Pending data env locals index st)
    (before after : V) (final : code.BodyState)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ depths fallback, Body.BrTable.Decoded data st.core.pos depths fallback final.core.pos := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_accepts st data env before () final after accepted
  cases unit
  have erased : code.branch_table st data env =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have contextWf := Body.Frames.enter_wf C
    (spine.context_wf (Translation.Environment.context_wf env ⟨locals,p.ft.results⟩)) p.current.form p.current.ins p.current.outs
  have labels := p.opened.branch_labels rfl C outer spine
  have effect := code.branch_table.prefix st data env _ p.current.ctrl outer p.current.vals controls values base
    p.opened.shape.core _ contextWf _ p.current.ops typed labels
  rw [erased,WP.spec_ok] at effect
  obtain ⟨depths,fallback,decoded,_⟩ := effect rfl
  exact ⟨depths,fallback,decoded⟩
end Itasca.Compiler

end

/-! ## Structured Reader Prefix Table Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_table {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    {jumpTables emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable=true → p.current.ctrl.polymorphic_base=false)
    (boundary : CompilerTableBoundary before)
    (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (Body.BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before=.ok (.Ok (),out,after)) :
    Body.ReaderPost p out.core (Body.BrTable.instruction depths fallback) true [] ∧
    StructuredCompilerPrefix jumpTables emit initial after types functions returns locals parents
      (current.advance (Body.BrTable.instruction depths fallback)) out.core.vals.val out.core.pos.val ∧
    CompilerTableBoundary after ∧ after.reachable=false := by
  have post := reader_table_post (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    p before after out depths fallback endPos byte encoded accepted
  have sourceAt : Body.At data p.start (.plain (Body.BrTable.instruction depths fallback)) endPos :=
    .plain (.of_table_decoded depths fallback p.inbounds byte p.pos encoded)
  have endEq := (post.encoded.unique sourceAt).2
  have consumed := table_immediate_byte_bound encoded
  have position := p.pos
  obtain ⟨_,_,_,afterBoundary,dead,_⟩ := compiler_reader_table_effect ops law before after st out
    data env p.opened.shape.core depths fallback endPos encoded boundary accepted
  refine ⟨post,?_,afterBoundary,dead⟩
  by_cases live : before.reachable=true
  · obtain ⟨entered,_⟩ := invariant.live live
    obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      entered (invariant.known live) (monomorphic live) before after out depths fallback endPos encoded accepted
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    have staged := invariant.table_scratch budget buffer
    exact staged.br_table ops law out.core depths fallback blockTypes stack stackEq inputs
      (by simpa only [boundary.depths,List.nil_append] using bufferEq) boundary.targets futureTables tableEq
      (gate stack) (by rw [endEq]; omega) live callback
  · have beforeDead := Bool.eq_false_iff.mpr live
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    obtain ⟨fixed,codeEq,_,frames,_,_,sources,cursor⟩ := compiler_br_table_dead_effect ops law
      {before with budget,table_depths := buffer} after out.core fallback blockTypes beforeDead callback
    have ordinary : CompilerOrdinaryStable before after := by
      refine ⟨?_,fixed.stable.capacity⟩
      change (compilerMetadata after,after.frames,after.function.controls)=
        (compilerMetadata before,before.frames,before.function.controls)
      rw [fixed.stable.metadata,frames,fixed.controls]
      rfl
    exact invariant.skip (Body.BrTable.instruction depths fallback) beforeDead dead ordinary codeEq sources
      (by rw [endEq]; omega) (by rw [cursor])
end Itasca.Compiler

end

/-! ## Structured Reader Compiler Table -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals
      data env ctx.locals index ft st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState) (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : Body.BrTable.Decoded data next depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (Body.BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index 0x0e#u8 before=.ok (.Ok (),out,after)) :
    StructuredReaderCompilerState jumpTables emit initial after types functions returns locals
      data env ctx.locals index ft out parents (current.advance (Body.BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (Body.BrTable.instruction depths fallback)) (Body.BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  rw [Body.CallbackTrace.dispatch_br_table] at accepted
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post,compiled,afterBoundary,dead⟩ := structured_reader_prefix_table p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current boundary depths fallback endPos encoded
    futureTables tableEq gate byte accepted
  refine ⟨state.advance next advance inbounds post ?_ compiled (by simp [dead]),afterBoundary⟩
  simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices,Body.BrTable.instruction]
end Itasca.Compiler

end

/-! ## Indexed Table Reader Table -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPoint.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals
      data env ctx.locals index ft st)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState)
    (gate : ∀ tables depths fallback stack selector start len,
      emit tables (stack++[.I32]) (Body.BrTable.instruction depths fallback) [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index 0x0e#u8 before=.ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have read := accepted
  rw [Body.CallbackTrace.dispatch_br_table] at read
  obtain ⟨depths,fallback,decoded⟩ := reader_table_decoded
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p before after out read
  obtain ⟨targets,tablesEq⟩ := compiler_reader_table_tables ops law before after _ out data env
    p.opened.shape.core depths fallback out.core.pos decoded read
  obtain ⟨_,_,_,boundary,_,_⟩ := compiler_reader_table_effect ops law before after _ out
    data env p.opened.shape.core depths fallback out.core.pos decoded point.tables read
  apply point.append_step ⟨[],[],[],targets⟩ tablesEq boundary
  intro future held
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := held
  obtain ⟨advanced,_⟩ := state.br_table ops law point.tables next advance inbounds out depths fallback out.core.pos decoded
    future.jumpTables rfl (gate _ depths fallback) byte accepted
  exact advanced.point
end Itasca.Compiler

end

end

/-! ## RootCompilation -/

section

/-!
Finishing the root scope of a structured reader state.

Main declarations: `StructuredReaderCompilerState.finish_root` and `StructuredReaderCompilerState.root_scopes`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.finish_root {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent source}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions (ft.results.val.map Translation.valueType) locals
      data env ctx.locals index ft st [] current [] savedCurrent)
    (root : savedCurrent.form = .body)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (encodedBody : Body.BodyEncoding data source)
    (byte : data.val[st.core.pos.val]'inbounds = 0x0b#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after))
    (rest : TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out after final) :
    StructuredCompiledBody jumpTables emit initial final types functions (ft.results.val.map Translation.valueType) locals source := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Body.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Body.outputs, Body.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Body.Stack.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Body.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translation.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Body.Stack.stackTypes st.core.vals.val = ft.results.val.map Translation.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Body.Stack.Realizes false savedCurrent.vals (savedCurrent.outs.map Translation.valueType) := by
      simpa [p, ReaderBoundary.pending, mono] using realizes
    have decoded := realized_concrete_types concrete actual
    simpa [rawEq, outs] using decoded.symm
  have closed : out.blocks.val = [] := by
    have generic := code.end_frame.sound _ env false [] [] savedCurrent.ctrl savedCurrent.bt savedCurrent.ins savedCurrent.outs
      [] savedCurrent.vals (by simpa [p, ReaderBoundary.pending] using controls)
      (by simpa [p, ReaderBoundary.pending] using blocks) (by simp)
      (by simp [rawEq]) (by simpa [outerEq] using base)
      header.inputs header.outputs p.opened.shape.core
    have erased : code.end_frame {core := {st.core with pos := next}} env false = .ok (.Ok (), out) := by
      simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
    rw [erased, WP.spec_ok] at generic
    exact (generic rfl).2.2.2.2.1
  obtain ⟨finalEq, finished⟩ := rest.closed closed
  subst final
  have complete : out.core.pos.val = data.length := by simpa using congrArg UScalar.val finished
  have sourceEq : current.source = source := state.sources.current.source.trans
    (reader_root_end_source p root encoded zipper complete encodedBody)
  have consumed : st.core.pos.val < out.core.pos.val := by have := encoded.span; omega
  have entry := state.compiled.entryChain.root_entered rfl
  have result := state.compiled.finish_body ops law entry stack sourceForm front params results out.core
    savedCurrent.ctrl.kind savedCurrent.bt (by omega) consumed (by omega) callback
  simpa only [StructuredCompiledBody, sourceEq] using result

theorem StructuredReaderCompilerState.root_scopes {jumpTables : List U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent)
    (root : savedCurrent.form = .body) : parents = [] ∧ savedParents = [] := by
  obtain ⟨C, outer, spine, _⟩ := state.boundary.opened
  rw [root] at spine
  have saved := spine.body.1
  have paired := state.sources.parents
  rw [saved] at paired
  cases paired
  exact ⟨rfl, saved⟩
end Itasca.Compiler

end
