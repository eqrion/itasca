import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Scalar.GlobalSelectAndSignCompilation
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerCompilation
import Itasca.Runtime.Compiler.Body.Reader.Float.Compilation
import Itasca.Runtime.Compiler.Body.Reader.Float.SaturatingCompilation
import Itasca.Runtime.Compiler.Body.Reader.References.StructuredCompilerTypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation

/-!
Sections, each formerly its own module: IndexedTablePointExtra, IndexedTablePointNumeric, IndexedTablePointTypedSelect.
-/

/-! ## IndexedTablePointExtra -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm2.core_extra {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_scalar_effects_wasm2 ops law before after _ out data env ctx _ opcode covered accepted
  apply point.preserved_step effects.tables effects.depths effects.code_mono
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : ScalarEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨(includeCumulative ((CompilerTables.ofFunction before.function).append future)).scalar⟩
  exact state.core_extra ops law C contextLocals contextGlobals contextMemories next advance inbounds out sourceBound bodyBound opcode covered byte accepted
end Itasca.Runtime.Compiler

end

/-! ## IndexedTablePointNumeric -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.float_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (floatOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_float_base_effects_wasm2 ops law before after _ out data env ctx _ op baseOpcode accepted
  apply point.preserved_step effects.tables effects.depths effects.code_mono
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : ScalarEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨(includeCumulative ((CompilerTables.ofFunction before.function).append future)).scalar⟩
  obtain ⟨values,changed⟩ := state.float_base ops law C contextLocals next advance inbounds out op baseOpcode
    sourceBound bodyBound byte accepted
  exact changed.point

theorem IndexedTableReaderCompilerPointWasm2.float_saturating {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (endPosition : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data next subopcode endPosition)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (252#u8))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index (252#u8) before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_saturating_effects_wasm2 p ops law before after out ctx op extension
    subopcode endPosition subopcodeEq decoded byte accepted
  apply point.preserved_step effects.tables effects.depths effects.code_mono
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : ScalarEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨(includeCumulative ((CompilerTables.ofFunction before.function).append future)).scalar⟩
  obtain ⟨values,changed⟩ := state.float_saturating ops law C contextLocals next advance inbounds out op extension
    subopcode endPosition subopcodeEq decoded sourceBound bodyBound byte accepted
  exact changed.point

end Itasca.Runtime.Compiler

end

/-! ## IndexedTablePointTypedSelect -/

section

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
      {core := {st.core with pos := next}} data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
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

end
