import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndElseCompilation
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCapacity
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Body.Control.ControlPointsAndInitialPrefixes
import Itasca.Runtime.Compiler.Body.Control.IndexedEntryCompilerInitial
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdCallbackPublication
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Body.Relations.ExecutableEmission
import Itasca.Runtime.Compiler.Local.Relations.Syntax.MiscOpcodes
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects FoldAndStatefulReplay, IndexedCompilerBody.
Each section documents its contracts and consumers.
-/

/-! ## FoldAndStatefulReplay -/

section

/-!
# Fold And Stateful Replay

Indexed callback folds preserve the replay relation. Stateful instruction cases extend the same fold invariant with their operand and object observations.
-/

/-! ## IndexedFold -/

section

/-!
Folding a typed source run while retaining compiler jump-table certificates.

Main declarations: `TypedRun.fold_indexed_tables`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem TypedRun.fold_indexed_tables {A : Type}
    (ops : runtime.platform.Alloc A)
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.wasm_types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source ∨
      IndexedTableReaderCompilerPoint emit initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env ctx.locals index ft st) :
    StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point.future CompilerTables.empty
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := state.boundary.opened
    rw [closed] at blocks
    simp at blocks
  | @step st before next out middle final typed pending start advance called rest ih =>
    have inbounds : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
    have called' : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) := by
      simpa only [start] using called
    rcases progress st before middle final next out point advance inbounds called' rest with done | nextPoint
    · exact done
    · exact ih nextPoint

end Itasca.Compiler

end

/-! ## StatefulFuturePrefix -/

section

/-!
A fixed future metadata table can be used on both sides of one actual stateful callback. Its current entries are retained by list append.

Main declarations: `StatefulReaderPost.future_prefix_generic`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- A fixed future metadata table can be used on both sides of one actual
stateful callback. Its current entries are retained by list append. -/
theorem StatefulReaderPost.future_prefix_generic {jumpTables : List U32} {data env sourceLocals index st}
    {p : Body.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context) (future : List (U32 × U32))
    {emit types functions returns locals parents current}
    [OrdinaryEmbedding (after.function.indirect.val ++ future) C emit]
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit
      initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, Body.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit
        initial after types functions returns locals parents (current.advance op.source) out.vals.val out.pos.val ∧
      after.reachable = before.reachable := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,pairs,values,emitted,output,reader,lowered,emission⟩ :=
      post.emission ops law before after C a b arguments callback matched
        (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
        retained.layout reachable codeFits sourceFits coordinateFits
    have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := reader.span; omega
    refine ⟨values,reader,invariant.ordinary reachable ordinary lowered (OrdinaryEmbedding.stateful (pairs := after.function.indirect.val ++ future) ((emission.map_pairs ?_)))
      sources consumed (by rw [cursor]) emission.not_branch_table,lowered.1.2.2.2.1⟩
    intro index pair found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simpa only [List.getElem?_append,if_pos bound] using found
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨values,reader,_⟩ := post
    have ordinary := compiler_stateful_ordinary_result ops law before after out op a b (.Ok ()) callback
    have sources := compiler_stateful_sources ops law before after out op a b callback
    have cursor := compiler_stateful_cursor ops law before after out op a b callback
    obtain ⟨compiled,deadAfter⟩ := reader.structured_skip ops law invariant dead ordinary sources cursor
      (statefulOpcode op) a b 0#u128 callback
    exact ⟨values,reader,compiled,deadAfter.trans dead.symm⟩

end Itasca.Compiler

end

/-! ## IndexedStateful -/

section

/-!
Stateful reader steps under the indexed compiler-table invariant.

Main declarations: `IndexedTableReaderCompilerPoint.stateful_reader` and `IndexedTableReaderCompilerPoint.stateful_bulk`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPoint.stateful_reader {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env sourceLocals index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env sourceLocals index ft st)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (read : ∀ p : Body.Pending data env sourceLocals index {core := {st.core with pos := next}},
      p.start = st.core.pos → ∃ op a b, StatefulArguments op a b ∧
        runtime.compiler.lower.FunctionCompiler.op ops before out.core (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after) ∧
        StatefulReaderPost p out.core op) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env sourceLocals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,a,b,arguments,callback,post⟩ := read p rfl
  obtain ⟨extra,pairs⟩ := post.indirect_prefix ops law initial before after C state.compiled
    state.reach.current matched contextLocals a b arguments callback sourceBound bodyBound
  have auxiliary := compiler_stateful_auxiliary_tables ops law before after out.core op a b (.Ok ()) callback
  have tables := compiler_tables_pair_append before.function after.function extra pairs auxiliary
  have depths := compiler_stateful_depths ops law before after out.core op a b (.Ok ()) callback
  have growth := compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback
  have jumps : after.function.jump_tables.val = before.function.jump_tables.val := by
    have h := congrArg CompilerTables.jumpTables tables
    simpa only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil] using h
  have boundary : CompilerTableBoundary after :=
    ⟨by simpa only [depths] using point.tables.depths,
      by simpa only [jumps] using point.tables.targets.trans growth⟩
  apply point.append_step ⟨extra,[],[],[]⟩ tables boundary
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,a,b,arguments,callback,post⟩ := read p rfl
  letI : OrdinaryEmbedding (after.function.indirect.val ++ future.indirect) C
      (emit ((CompilerTables.ofFunction after.function).append future)) := embedding ((CompilerTables.ofFunction after.function).append future)
  obtain ⟨values,reader,compiled,reachable⟩ := post.future_prefix_generic ops law initial before after C future.indirect state.compiled
    state.reach.current matched contextLocals a b arguments callback sourceBound bodyBound
  exact (state.advance next advance inbounds reader reader.declared compiled
    (fun live => state.reach.current (reachable ▸ live))).point

theorem IndexedTableReaderCompilerPoint.stateful_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env ctx.locals index ft st)
    (matched : Translation.Environment.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law embedding matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member
    (by simpa only [start] using byte) accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

theorem IndexedTableReaderCompilerPoint.stateful_bulk {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env ctx.locals index ft st)
    (matched : Translation.Environment.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (subopcode : U32) (afterSubopcode : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (decoded : Binary.Leb128.Decoded data next subopcode afterSubopcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law embedding matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode afterSubopcode member
    (by simpa only [start] using byte) decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

end Itasca.Compiler

end

end

/-! ## IndexedCompilerBody -/

section

/-!
Actual accepted complete body execution produces indexed code evidence against all four final function-local tables.

Main declarations: `TypedRun.compile_executable`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- Actual accepted complete body execution produces indexed code
evidence against all four final function-local tables. -/
theorem TypedRun.compile_executable {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (C : context)
    (run : TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) initial before (env.types.val.map Translation.Environment.funcType)
      (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st)
    (encoded : Body.BodyEncoding data source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody final.function.jump_tables.val ((fun tables => ExecutableEmission tables C) (CompilerTables.ofFunction final.function)) initial final
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (ft.results.val.map Translation.valueType) locals source := by
  apply TypedRun.fold_indexed_tables ops (fun tables => ExecutableEmission tables C) initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := encoded.next_reader_opcode state.boundary.consumed inbounds
  rcases allowed with ordinary | scope | isElse | isEnd | extra | floatBase | memoryOp | indirect | table | statefulOp | prefixed | simd | typedSelect
  · exact .inr (point.ordinary ops law contextLocals (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) metadata localsMatch next advance inbounds out sourceBound bodyBound
      _ ordinary rfl accepted)
  · exact .inr (point.scope_step ops law next advance inbounds out sourceBound signatures _ scope rfl accepted)
  · rw [isElse] at accepted
    exact .inr (point.else_ ops law next advance inbounds out initialLocals
      (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
  · rw [isEnd] at accepted
    by_cases root : st.blocks.val.length = 1
    · exact .inl (point.finish_root ops law root next advance inbounds out sourceBound bodyBound encoded isEnd accepted rest)
    · exact .inr (point.end_nested ops law next advance inbounds out initialLocals rfl root bodyBound
        (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
  · exact .inr (point.core_extra ops law C (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals matched.globals matched.mems
      next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
  · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
    rw [← equal] at accepted
    exact .inr (point.float_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
  · have stateful := stateful_opcode_values (.inl memoryOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · rw [indirect] at accepted
    exact .inr (point.indirect_call ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C)))
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
  · rw [table] at accepted
    exact .inr (point.br_table ops law next advance inbounds out
      (by intro tables depths fallback stack selector start len; exact .branchTable _ _ _ _ _ _) table accepted)
  · have stateful := stateful_opcode_values (.inr statefulOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · obtain ⟨subopcode,endPosition,decoded,choice⟩ :=
      encoded.next_misc state.boundary.consumed inbounds next advance prefixed
    rw [prefixed] at accepted
    rcases choice with ⟨op,extension,subopcodeEq⟩ | bulk
    · exact .inr (point.float_saturating ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op extension
        subopcode endPosition subopcodeEq decoded sourceBound bodyBound prefixed accepted)
    · exact .inr (point.stateful_bulk ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out subopcode endPosition bulk
        sourceBound bodyBound prefixed decoded accepted)
  · rw [simd] at accepted
    exact .inr (point.simd ops law C contextLocals matched.mems (fun tables => (inferInstance : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C))) next advance inbounds out sourceBound bodyBound simd accepted)
  · rw [typedSelect] at accepted
    exact .inr (point.typed_select ops law C (by intro tables input instruction code output h; exact .typedSelect h) contextLocals next advance inbounds out sourceBound bodyBound typedSelect accepted)
end Itasca.Compiler

end
