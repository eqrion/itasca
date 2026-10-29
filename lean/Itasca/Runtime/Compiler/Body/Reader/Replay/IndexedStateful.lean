import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Reader.Replay.PostDeclared
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerPairTableAppend
import Itasca.Runtime.Compiler.Body.Reader.Replay.StatefulFuturePrefix
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch

/-!
Stateful reader steps under the indexed compiler-table invariant.

Main declarations: `IndexedTableReaderCompilerPointWasm2.stateful_reader` and `IndexedTableReaderCompilerPointWasm2.stateful_bulk`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerBodyWasm2`.
-/

namespace Itasca.Runtime.Code
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
    (read : ∀ p : Wasm2.Pending data env .Wasm2 sourceLocals index {core := {st.core with pos := next}},
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  apply point.stateful_reader ops law embedding matched contextLocals next advance inbounds out sourceBound bodyBound
  intro p start
  obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode afterSubopcode member
    (by simpa only [start] using byte) decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact ⟨op,a,b,arguments,callback,post⟩

end Itasca.Runtime.Code
