import Exec.Code.Body.Control.Common.CumulativePointWasm1
import Exec.Code.Body.Reader.Calls.ReaderIndirectPairPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem CumulativeReaderCompilerPointWasm1.indirect_call_with {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx bodyBt st}
    (point : CumulativeReaderCompilerPointWasm1 C initial before types functions returns locals data env ctx bodyBt st)
    (embedding : ∀ pairs input instruction emitted output,
      IndirectCallEmission pairs C input instruction emitted output → CumulativeEmission pairs C input instruction emitted output)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 17#u8 before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm1 C initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  obtain ⟨extra,pairs⟩ := reader_indirect_call_pair_prefix_wasm1 p ops law initial before after out C
    state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte
    (by simpa only [global_simps] using accepted)
  apply point.append_step extra pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨index,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call_wasm1 p ops law initial before after out C future
      (embedding _) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte
      (by simpa only [global_simps] using accepted)
  exact (state.advance next advance inbounds reader compiled
    (fun live => state.reach.current (reachable ▸ live))).point

theorem CumulativeReaderCompilerPointWasm2.indirect_call_with {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (embedding : ∀ pairs input instruction emitted output,
      IndirectCallEmission pairs C input instruction emitted output → CumulativeEmission pairs C input instruction emitted output)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  obtain ⟨extra,pairs⟩ := reader_indirect_call_pair_prefix_wasm2 p ops law initial before after out ctx C
    state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  apply point.append_step extra pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨typeIndex,table,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call_wasm2 p ops law initial before after out ctx C future
      (embedding _) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  exact (state.advance next advance inbounds reader (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reachable ▸ live))).point
end Exec.Code
