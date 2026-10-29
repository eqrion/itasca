import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerCompilation
import Itasca.Runtime.Compiler.Body.Reader.Float.Compilation
import Itasca.Runtime.Compiler.Body.Reader.Float.SaturatingCompilation
namespace Itasca.Runtime.Code
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
    (out : code.BodyState) (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (floatOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
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
    (out : code.BodyState) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (endPosition : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data next subopcode endPosition)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (252#u8))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (252#u8) before = .ok (.Ok (),out,after)) :
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

end Itasca.Runtime.Code
