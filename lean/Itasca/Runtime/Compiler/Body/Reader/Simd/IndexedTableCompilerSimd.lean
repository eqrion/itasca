import Itasca.Runtime.Compiler.Body.Reader.Simd.Prefix
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdStaticTables
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEventTables

/-!
SIMD compilation under the structured reader invariant and the indexed compiler-table invariant.
-/

/-! ## Structured Reader Compiler Simd -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual SIMD dispatch extends the same canonical source zipper and the
structured compiler state, including dead code and exact table growth. -/
theorem StructuredReaderCompilerStateWasm2.simd {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C contextMemories byte accepted
  obtain ⟨extra,tables,compiled,mono⟩ := event.prefix law contextLocals state.compiled
    state.reach.current sourceBound bodyBound
  exact ⟨extra,tables,(state.advance next advance inbounds event.post (event.meaning.declared _) compiled mono).point⟩
end Itasca.Runtime.Code

end

/-! ## Indexed Table Reader Compiler Simd -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- SIMD dispatch preserves the compiler point quantified over future
extensions of every function table. The append witness comes from the actual
accepted callback before the old point is reindexed. -/
theorem IndexedTableReaderCompilerPointWasm2.simd {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, SimdEmbedding tables.simd tables.constants C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C contextMemories byte accepted
  obtain ⟨extra,tables⟩ := event.tables law contextLocals state.compiled state.reach.current sourceBound bodyBound
  have depths := event.depths law
  have growth := event.code_mono law
  have bound := event.meaning.opcode_bound
  have number := event.number
  have jumps := (compiler_lower_simd_preserved_tables ops law before after out.core
    event.opcode event.a event.b event.bits (by omega) (by omega) event.callback).2
  have boundary : CompilerTableBoundary after :=
    ⟨by simpa only [depths] using point.tables.depths,
      by simpa only [jumps] using point.tables.targets.trans growth⟩
  apply point.append_step extra tables boundary
  intro future beforePoint
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := beforePoint
  letI : SimdEmbedding ((CompilerTables.ofFunction after.function).append future).simd
      ((CompilerTables.ofFunction after.function).append future).constants C
      (emit ((CompilerTables.ofFunction after.function).append future)) := embedding _
  letI : SimdEmbedding after.function.simd.val after.function.v128_pool.val C
      (emit ((CompilerTables.ofFunction after.function).append future)) :=
    ⟨fun h => (embedding ((CompilerTables.ofFunction after.function).append future)).lift
      (h.append_tables future.simd future.constants)⟩
  obtain ⟨_,_,nextPoint⟩ := state.simd ops law C contextLocals contextMemories next advance inbounds out
    sourceBound bodyBound byte accepted
  exact nextPoint
end Itasca.Runtime.Code

end
