import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Reader.References.StructuredCompilerTypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.typed_select {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables input instruction code output,
      TypedSelectEmission C input instruction code output → emit tables input instruction code output)
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have pairs := compiler_core_tables ops law before after out.core (.select true) callback
  have depths := reader_typed_select_depths_wasm2 p ops law before after out ctx byte accepted
  have growth := reader_typed_select_code_mono_wasm2 p ops law before after out ctx byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.typed_select ops law C (fun h => embedding _ _ _ _ _ h) contextLocals next advance inbounds out
    sourceBound bodyBound byte accepted
end Itasca.Runtime.Compiler
