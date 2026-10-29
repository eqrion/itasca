import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalBranchTable
import Itasca.Runtime.Compiler.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallbackLayout
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableScopeFrames
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableGrowth
import Itasca.Runtime.Compiler.Local.Relations.Table.TableSources
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTablePost
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableInputsWasm2
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState
import Itasca.Wasm2.Trace.TableBytes
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Relations.Table.BranchTableTables

/-!
Indexed br_table compilation from the decoded reader instruction through source prefixes and scratch tables. The final theorem retains the complete indexed compiler-table relation.
-/

/-! ## Structured Compiler Prefix Table -/

section

namespace Itasca.Runtime.Compiler
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
    (stack : List valtype) (stackEq : Sequence.stackTypes raw = stack ++ [.I32])
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
end Itasca.Runtime.Compiler

end

/-! ## Structured Table Scratch -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## Reader Table Decoded -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_table_decoded_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (before after : V) (final : code.BodyState)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ∃ depths fallback, BrTable.Decoded data st.core.pos depths fallback final.core.pos := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after _ accepted
  cases unit
  have erased : code.branch_table st data env .Wasm2 =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have contextWf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩)) p.current.form p.current.ins p.current.outs
  have labels := p.opened.branchLabels rfl C outer spine
  have effect := code.branch_table.prefix st data env .Wasm2 _ p.current.ctrl outer p.current.vals controls values base
    p.opened.shape.core _ contextWf _ p.current.ops typed labels
  rw [erased,WP.spec_ok] at effect
  obtain ⟨depths,fallback,decoded,_⟩ := effect rfl
  exact ⟨depths,fallback,decoded⟩
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Table Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_table_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    {jumpTables emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable=true → p.current.ctrl.polymorphic_base=false)
    (boundary : CompilerTableBoundary before)
    (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before=.ok (.Ok (),out,after)) :
    Wasm2.ReaderPost p out.core (BrTable.instruction depths fallback) true [] ∧
    StructuredCompilerPrefix jumpTables emit initial after types functions returns locals parents
      (current.advance (BrTable.instruction depths fallback)) out.core.vals.val out.core.pos.val ∧
    CompilerTableBoundary after ∧ after.reachable=false := by
  have post := reader_table_post_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    p before after out depths fallback endPos byte encoded accepted
  have sourceAt : Wasm2.At data p.start (.plain (BrTable.instruction depths fallback)) endPos :=
    .plain (.of_table_decoded depths fallback p.inbounds byte p.pos encoded)
  have endEq := (post.encoded.unique sourceAt).2
  have consumed := table_immediate_byte_bound encoded
  have position := p.pos
  obtain ⟨_,_,_,afterBoundary,dead,_⟩ := compiler_reader_table_effect_wasm2 ops law before after st out
    data env p.opened.shape.core depths fallback endPos encoded boundary accepted
  refine ⟨post,?_,afterBoundary,dead⟩
  by_cases live : before.reachable=true
  · obtain ⟨entered,_⟩ := invariant.live live
    obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      entered (invariant.known live) (monomorphic live) before after out depths fallback endPos encoded accepted
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    have staged := invariant.table_scratch budget buffer
    exact staged.br_table ops law out.core depths fallback blockTypes stack stackEq inputs
      (by simpa only [boundary.depths,List.nil_append] using bufferEq) boundary.targets futureTables tableEq
      (gate stack) (by rw [endEq]; omega) live callback
  · have beforeDead := Bool.eq_false_iff.mpr live
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    obtain ⟨fixed,codeEq,_,frames,_,_,sources,cursor⟩ := compiler_br_table_dead_effect ops law
      {before with budget,table_depths := buffer} after out.core fallback blockTypes beforeDead callback
    have ordinary : CompilerOrdinaryStable before after := by
      refine ⟨?_,fixed.stable.capacity⟩
      change (compilerMetadata after,after.frames,after.function.controls)=
        (compilerMetadata before,before.frames,before.function.controls)
      rw [fixed.stable.metadata,frames,fixed.controls]
      rfl
    exact invariant.skip (BrTable.instruction depths fallback) beforeDead dead ordinary codeEq sources
      (by rw [endEq]; omega) (by rw [cursor])
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Table -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals
      data env ctx.locals index ft st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState) (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data next depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) :
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals
      data env ctx.locals index ft out parents (current.advance (BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (BrTable.instruction depths fallback)) (BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post,compiled,afterBoundary,dead⟩ := structured_reader_prefix_table_wasm2 p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current boundary depths fallback endPos encoded
    futureTables tableEq gate byte accepted
  refine ⟨state.advance next advance inbounds post ?_ compiled (by simp [dead]),afterBoundary⟩
  simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices,BrTable.instruction]
end Itasca.Runtime.Compiler

end

/-! ## Indexed Table Reader Table -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals
      data env ctx.locals index ft st)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState)
    (gate : ∀ tables depths fallback stack selector start len,
      emit tables (stack++[.I32]) (BrTable.instruction depths fallback) [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have read := accepted
  rw [Wasm2.CallbackTrace.dispatch_br_table] at read
  obtain ⟨depths,fallback,decoded⟩ := reader_table_decoded_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p before after out read
  obtain ⟨targets,tablesEq⟩ := compiler_reader_table_tables_wasm2 ops law before after _ out data env
    p.opened.shape.core depths fallback out.core.pos decoded read
  obtain ⟨_,_,_,boundary,_,_⟩ := compiler_reader_table_effect_wasm2 ops law before after _ out
    data env p.opened.shape.core depths fallback out.core.pos decoded point.tables read
  apply point.append_step ⟨[],[],[],targets⟩ tablesEq boundary
  intro future held
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := held
  obtain ⟨advanced,_⟩ := state.br_table ops law point.tables next advance inbounds out depths fallback out.core.pos decoded
    future.jumpTables rfl (gate _ depths fallback) byte accepted
  exact advanced.point
end Itasca.Runtime.Compiler

end
