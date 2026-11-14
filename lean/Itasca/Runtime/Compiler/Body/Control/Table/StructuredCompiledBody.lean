import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal

/-!
Sections, each formerly its own module: IndexedTablePointIndirectCall, StructuredLinearEmbedding, StructuredCompiledBody.
-/

/-! ## IndexedTablePointIndirectCall -/

section

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
      {core := {st.core with pos := next}} data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
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

end

/-! ## StructuredLinearEmbedding -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.ordinary_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branch_table

theorem StructuredCompilerPrefix.ordinary_empty_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary_empty reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branch_table
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompiledBody -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
/-- Completed source-to-bytecode evidence, before the compiler's final
well-formedness check packages the executable function. -/
def StructuredCompiledBody (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (initial final : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype) (source : List instr) : Prop :=
  ∃ target : U32, CompilerStable initial final ∧ final.frames.val = [] ∧
    StructuredCode emit types functions returns locals final.function.code.val jumpTables
      [functionRootLabel returns final.function target] [] source 0 target.val returns ∧
    (∃ src count, src.val = slots locals ∧ final.function.code.val[target.val]? = some (.Return src count)) ∧
    final.function.code.val.length = target.val + 1 ∧ final.function.code.val.length ≤ U32.max

end Itasca.Runtime.Compiler

end
