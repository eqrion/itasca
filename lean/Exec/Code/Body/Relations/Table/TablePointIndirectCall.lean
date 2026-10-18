import Exec.Code.Body.Reader.Table.TableReaderCompilerPoint
import Exec.Code.Local.Callbacks.Table.CompilerPairTableAppend
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Calls.ReaderIndirectPairPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem TableReaderCompilerPointWasm1.indirect_call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : TableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (embedding : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 17#u8 before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  obtain ⟨extra,pairs⟩ := reader_indirect_call_pair_prefix_wasm1 p ops law initial before after out C
    state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte
    (by simpa only [global_simps] using accepted)
  have capacity : {st with pos := next}.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨idx,_,callback,_,_⟩ := reader_indirect_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte
    (by simpa only [global_simps] using accepted)
  change runtime.compiler.lower.FunctionCompiler.op ops before out 17#u16 idx 0#u32 0#u128 = _ at callback
  have auxiliary := compiler_indirect_call_auxiliary_tables ops law before after out idx 0#u32 (.Ok ()) callback
  have tables := compiler_tables_pair_append before.function after.function extra pairs auxiliary
  apply point.append_step ⟨extra,[],[],[]⟩ tables
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨index,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call_wasm1 p ops law initial before after out C future.indirect
      (fun _ _ _ _ head => (embedding ((CompilerTables.ofFunction after.function).append future)).lift (.indirect head)) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte
      (by simpa only [global_simps] using accepted)
  exact (state.advance next advance inbounds reader compiled
    (fun live => state.reach.current (reachable ▸ live))).point

theorem TableReaderCompilerPointWasm2.indirect_call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (embedding : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
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
  apply point.append_step ⟨extra,[],[],[]⟩ tables
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨typeIndex,table,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call_wasm2 p ops law initial before after out ctx C future.indirect
      (fun _ _ _ _ head => (embedding ((CompilerTables.ofFunction after.function).append future)).lift (.indirect head)) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  exact (state.advance next advance inbounds reader (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reachable ▸ live))).point
end Exec.Code
