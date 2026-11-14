import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Reader.Control.RootCompilation
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch

/-!
Sections, each formerly its own module: IndexedFold, StatefulFuturePrefix, IndexedStateful.
-/

/-! ## IndexedFold -/

section

/-!
Folding a typed source run while retaining compiler jump-table certificates.

Main declarations: `TypedRunWasm2.fold_indexed_tables`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerBodyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem TypedRunWasm2.fold_indexed_tables {A : Type}
    (ops : runtime.platform.Alloc A)
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.wasm_types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source ∨
      IndexedTableReaderCompilerPointWasm2 emit initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st) :
    StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point.future CompilerTables.empty
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := state.boundary.opened
    rw [closed] at blocks
    simp at blocks
  | @step st before next out middle final typed pending start advance called rest ih =>
    have inbounds : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
    have called' : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) := by
      simpa only [start] using called
    rcases progress st before middle final next out point advance inbounds called' rest with done | nextPoint
    · exact done
    · exact ih nextPoint

end Itasca.Runtime.Compiler

end

/-! ## StatefulFuturePrefix -/

section

/-!
A fixed future metadata table can be used on both sides of one actual stateful callback. Its current entries are retained by list append.

Main declarations: `StatefulReaderPost.future_prefix_generic`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedStateful`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
/-- A fixed future metadata table can be used on both sides of one actual
stateful callback. Its current entries are retained by list append. -/
theorem StatefulReaderPost.future_prefix_generic {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context) (future : List (U32 × U32))
    {emit types functions returns locals parents current}
    [OrdinaryEmbedding (after.function.indirect.val ++ future) C emit]
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit
      initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, Wasm2.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
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

end Itasca.Runtime.Compiler

end

/-! ## IndexedStateful -/

section

/-!
Stateful reader steps under the indexed compiler-table invariant.

Main declarations: `IndexedTableReaderCompilerPointWasm2.stateful_reader` and `IndexedTableReaderCompilerPointWasm2.stateful_bulk`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerBodyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.stateful_reader {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env sourceLocals index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env sourceLocals index ft st)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (read : ∀ p : Wasm2.Pending data env sourceLocals index {core := {st.core with pos := next}},
      p.start = st.core.pos → ∃ op a b, StatefulArguments op a b ∧
        runtime.compiler.lower.FunctionCompiler.op ops before out.core (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after) ∧
        StatefulReaderPost p out.core op) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
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

theorem IndexedTableReaderCompilerPointWasm2.stateful_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law embedding matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member
    (by simpa only [start] using byte) accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

theorem IndexedTableReaderCompilerPointWasm2.stateful_bulk {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (subopcode : U32) (afterSubopcode : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (decoded : Leb128.Decoded data next subopcode afterSubopcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law embedding matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode afterSubopcode member
    (by simpa only [start] using byte) decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

end Itasca.Runtime.Compiler

end
