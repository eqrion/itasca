import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
import Exec.Code.Body.Reader.Calls.ReaderScalarIndirect
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerNumeric
import Exec.Code.Body.Reader.Float.StructuredReaderCompilerFloat
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerSaturating
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CumulativeReaderCompilerPointWasm2.numeric {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Numeric.Instruction) 
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_numeric_indirect_wasm2 p ops law before after out ctx rfl op byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  have embedding : LinearEmbedding locals (CumulativeEmission (before.function.indirect.val ++ future) C) := by
    intro input instruction code output head
    exact .left (.core (.pure (by simpa only [contextLocals] using head)))
  obtain ⟨values,changed⟩ := state.numeric ops law embedding next advance inbounds out op sourceBound bodyBound byte accepted
  exact changed.point

theorem CumulativeReaderCompilerPointWasm2.float_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (floatOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_float_base_indirect_wasm2 p ops law before after out ctx rfl op baseOpcode byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  obtain ⟨values,changed⟩ := state.float_base ops law C contextLocals next advance inbounds out op baseOpcode
    sourceBound bodyBound byte accepted
  exact changed.point

theorem CumulativeReaderCompilerPointWasm2.float_saturating {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st)
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
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_saturating_indirect_wasm2 p ops law before after out ctx op extension
    subopcode endPosition subopcodeEq decoded byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  obtain ⟨values,changed⟩ := state.float_saturating ops law C contextLocals next advance inbounds out op extension
    subopcode endPosition subopcodeEq decoded sourceBound bodyBound byte accepted
  exact changed.point

end Exec.Code
