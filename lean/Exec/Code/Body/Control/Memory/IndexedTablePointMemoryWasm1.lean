import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPreserved
import Exec.Code.Body.Reader.Table.StatefulReaderPrefixGenericWasm1WithTables
import Exec.Code.Body.Reader.Memory.ReaderMemoryMetadataIndirectWasm1
import Exec.Code.Local.Callbacks.Table.CompilerPairTableAppend
import Exec.Code.Body.Reader.Common.ReaderExtendedScratch
import Exec.Code.Body.Reader.Common.ReaderExtendedCodeMonotone
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm1.memory_metadata {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (opcode : U8) (member : opcode.val ∈ [63,64])
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,single,arguments,callback,post⟩ := reader_stateful_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out opcode member byte accepted
  rw [stateful_callback_lower ops before out op 0#u32 0#u32 arguments] at callback
  have indirect := compiler_stateful_single_indirect ops law before after out op 0#u32 0#u32 single callback
  have auxiliary := compiler_stateful_auxiliary_tables ops law before after out op 0#u32 0#u32 (.Ok ()) callback
  have tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
    simpa only [CompilerTables.append, List.append_nil] using compiler_tables_pair_append before.function after.function []
      (by simp only [indirect,List.append_nil]) auxiliary
  have depths := compiler_stateful_depths ops law before after out op 0#u32 0#u32 (.Ok ()) callback
  have growth := compiler_stateful_code_mono ops law before after out op 0#u32 0#u32 (.Ok ()) callback
  apply point.preserved_step tables depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨op,single,arguments,callback,post⟩ := reader_stateful_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out opcode member byte accepted
  rw [stateful_callback_lower ops before out op 0#u32 0#u32 arguments] at callback
  letI := includeCumulative ((CompilerTables.ofFunction before.function).append future)
  obtain ⟨values,reader,compiled,reachable⟩ := post.single_prefix_generic_with_tables ops law initial before after C
    ((CompilerTables.ofFunction before.function).append future).indirect state.compiled
    state.reach.current matched contextLocals 0#u32 0#u32 single arguments callback sourceBound bodyBound
  exact (state.advance next advance inbounds reader compiled
    (fun live => state.reach.current (reachable ▸ live))).point
end Exec.Code
