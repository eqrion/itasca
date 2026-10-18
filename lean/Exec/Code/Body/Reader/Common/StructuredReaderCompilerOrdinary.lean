import Exec.Code.Body.Reader.Common.ReaderCompilerOrdinary
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerNumeric
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerConstants
import Exec.Code.Body.Reader.Local.StructuredReaderCompilerLocal
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerEmpty
import Exec.Code.Body.Reader.Calls.StructuredReaderCompilerCall
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerTerminal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWasm1.ordinary_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm1 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (opcode : U8) (ordinary : opcode ∈ readerBaseOrdinaryOpcodes)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  simp only [readerBaseOrdinaryOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (state.unreachable ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, changed⟩ := state.nop ops law embedding next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · exact (state.return_ ops law next advance inbounds out sourceBound bodyBound bodyResults (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, _, changed⟩ := state.call ops law metadata next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.drop ops law embedding next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_get ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_set ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_tee ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const32 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const64 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I32)) = 69#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I32) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 .EQ)) = 70#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 (.LT .U))) = 73#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I64)) = 80#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I64) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 .EQ)) = 81#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 (.LT .U))) = 84#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .ADD)) = 106#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .SUB)) = 107#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .ADD)) = 124#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .SUB)) = 125#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point

/-- Actual accepted ordinary dispatch preserves the retained compiler/source
point. All opcode-specific stack and callback facts are derived internally. -/
theorem StructuredReaderCompilerStateWasm2.ordinary_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerBaseOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  simp only [readerBaseOrdinaryOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (state.unreachable ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, changed⟩ := state.nop ops law embedding next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · exact (state.return_ ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, _, changed⟩ := state.call ops law metadata next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.drop ops law embedding next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_get ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_set ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_tee ops law embedding next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const32 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const64 ops law embedding next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I32)) = 69#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I32) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 .EQ)) = 70#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I32 (.LT .U))) = 73#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I32 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.eqz .I64)) = 80#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.eqz .I64) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 .EQ)) = 81#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 .EQ) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.compare .I64 (.LT .U))) = 84#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.compare .I64 (.LT .U)) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .ADD)) = 106#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I32 .SUB)) = 107#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I32 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .ADD)) = 124#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .ADD) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (integerOpcode (.binary .I64 .SUB)) = 125#u8 := by rfl
    obtain ⟨_, changed⟩ := state.numeric ops law embedding next advance inbounds out (.binary .I64 .SUB) sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point

theorem StructuredReaderCompilerStateWasm1.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm1 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact state.ordinary_base ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults opcode base byte accepted
  · obtain ⟨op, rfl⟩ := integer_opcode_of_mem numeric
    obtain ⟨values, changed⟩ := state.numeric ops law embedding next advance inbounds out op sourceBound bodyBound byte accepted
    exact changed.point

theorem StructuredReaderCompilerStateWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact state.ordinary_base ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode base byte accepted
  · obtain ⟨op, rfl⟩ := integer_opcode_of_mem numeric
    obtain ⟨values, changed⟩ := state.numeric ops law embedding next advance inbounds out op sourceBound bodyBound byte accepted
    exact changed.point

theorem StructuredReaderCompilerPointWasm1.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx bodyBt st}
    (embedding : LinearEmbedding locals emit)
    (point : StructuredReaderCompilerPointWasm1 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  exact state.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults opcode ordinary byte accepted

theorem StructuredReaderCompilerPointWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types locals data env ctx index ft st}
    (embedding : LinearEmbedding locals emit)
    (point : StructuredReaderCompilerPointWasm2 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  exact state.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Exec.Code
