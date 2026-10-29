import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Body.Reader.Calls.IndirectCallPrefix
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerPairTableAppend
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Calls.IndirectPairPrefix
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.indirect_call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  obtain ⟨extra,pairs⟩ := reader_indirect_call_pair_prefix_wasm2 p ops law initial before after out ctx C
    state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  obtain ⟨idx,tab,_,callback,_,_⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 idx tab 0#u128 = _ at callback
  have auxiliary := compiler_indirect_call_auxiliary_tables ops law before after out.core idx tab (.Ok ()) callback
  have tables := compiler_tables_pair_append before.function after.function extra pairs auxiliary
  have depths := reader_indirect_call_depths_wasm2 p ops law before after out ctx byte accepted
  have growth := reader_indirect_call_code_mono_wasm2 p ops law before after out ctx byte accepted
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
  obtain ⟨typeIndex,table,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call_wasm2 p ops law initial before after out ctx C future.indirect
      (fun _ _ _ _ head => (embedding ((CompilerTables.ofFunction after.function).append future)).indirect (head)) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  exact (state.advance next advance inbounds reader (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reachable ▸ live))).point
end Itasca.Runtime.Compiler
