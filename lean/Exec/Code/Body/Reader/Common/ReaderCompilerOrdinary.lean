import Exec.Code.Body.Reader.Common.ReaderCompilerNumeric
import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Reader.Common.ReaderCompilerConstants
import Exec.Code.Body.Reader.Integer.ReaderCompilerIntegers
import Exec.Code.Body.Reader.Local.ReaderCompilerLocal
import Exec.Code.Body.Reader.Common.ReaderCompilerEmpty
import Exec.Code.Body.Reader.Calls.ReaderCompilerCall
import Exec.Code.Body.Reader.Common.ReaderCompilerTerminal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Ordinary opcodes in the first compiler/execution slice. Structured openers,
branches, ELSE and END are handled by the source-zipper dispatcher. -/
def readerBaseOrdinaryOpcodes : List U8 :=
  [0x00#u8, 0x01#u8, 0x0f#u8, 0x10#u8, 0x1a#u8, 0x20#u8, 0x21#u8, 0x22#u8,
   0x41#u8, 0x42#u8, 0x45#u8, 0x46#u8, 0x49#u8, 0x50#u8, 0x51#u8, 0x54#u8,
   0x6a#u8, 0x6b#u8, 0x7c#u8, 0x7d#u8]

def readerOrdinaryOpcodes : List U8 := readerBaseOrdinaryOpcodes ++ integerOpcodes

/-- Actual accepted ordinary dispatch preserves the retained compiler/source
point. All opcode-specific stack and callback facts are derived internally. -/
theorem ReaderCompilerStateWasm1.ordinary_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
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
    ReaderCompilerPointWasm1 initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  simp only [readerBaseOrdinaryOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (state.unreachable ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, changed⟩ := state.nop ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · exact (state.return_ ops law next advance inbounds out sourceBound bodyBound bodyResults (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, _, changed⟩ := state.call ops law metadata next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.drop ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_get ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_set ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_tee ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const32 ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const64 ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (eqzOpcode .I32) = 69#u8 := by rfl
    obtain ⟨_, changed⟩ := state.eqz ops law next advance inbounds out .I32 sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .eq) = 70#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .eq sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .ltU) = 73#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .ltU sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (eqzOpcode .I64) = 80#u8 := by rfl
    obtain ⟨_, changed⟩ := state.eqz ops law next advance inbounds out .I64 sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .eq) = 81#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .eq sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .ltU) = 84#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .ltU sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .add) = 106#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .add sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .sub) = 107#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .sub sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .add) = 124#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .add sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .sub) = 125#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .sub sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point

/-- Actual accepted ordinary dispatch preserves the retained compiler/source
point. All opcode-specific stack and callback facts are derived internally. -/
theorem ReaderCompilerStateWasm2.ordinary_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
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
    ReaderCompilerPointWasm2 initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  simp only [readerBaseOrdinaryOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (state.unreachable ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, changed⟩ := state.nop ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · exact (state.return_ ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).point
  · obtain ⟨_, _, changed⟩ := state.call ops law metadata next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.drop ops law next advance inbounds out  (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_get ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_set ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, _, changed⟩ := state.local_tee ops law next advance inbounds out localsMatch sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const32 ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · obtain ⟨_, changed⟩ := state.const64 ops law next advance inbounds out sourceBound bodyBound (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (eqzOpcode .I32) = 69#u8 := by rfl
    obtain ⟨_, changed⟩ := state.eqz ops law next advance inbounds out .I32 sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .eq) = 70#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .eq sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .ltU) = 73#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .ltU sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (eqzOpcode .I64) = 80#u8 := by rfl
    obtain ⟨_, changed⟩ := state.eqz ops law next advance inbounds out .I64 sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .eq) = 81#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .eq sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .ltU) = 84#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .ltU sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .add) = 106#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .add sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I32 .sub) = 107#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I32 .sub sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .add) = 124#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .add sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point
  · have castOpcode : UScalar.cast .U8 (binaryOpcode .I64 .sub) = 125#u8 := by rfl
    obtain ⟨_, changed⟩ := state.integer ops law next advance inbounds out .I64 .sub sourceBound bodyBound (by simpa only [castOpcode] using byte) (by simpa only [castOpcode] using accepted)
    exact changed.point

theorem ReaderCompilerStateWasm1.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
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
    ReaderCompilerPointWasm1 initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact state.ordinary_base ops law metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults opcode base byte accepted
  · obtain ⟨op, rfl⟩ := integer_opcode_of_mem numeric
    obtain ⟨values, changed⟩ := state.numeric ops law next advance inbounds out op sourceBound bodyBound byte accepted
    exact changed.point

theorem ReaderCompilerStateWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
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
    ReaderCompilerPointWasm2 initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  rcases List.mem_append.mp ordinary with base | numeric
  · exact state.ordinary_base ops law metadata localsMatch next advance inbounds out sourceBound bodyBound opcode base byte accepted
  · obtain ⟨op, rfl⟩ := integer_opcode_of_mem numeric
    obtain ⟨values, changed⟩ := state.numeric ops law next advance inbounds out op sourceBound bodyBound byte accepted
    exact changed.point

theorem ReaderCompilerPointWasm1.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx bodyBt st}
    (point : ReaderCompilerPointWasm1 initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
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
    ReaderCompilerPointWasm1 initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  exact state.ordinary ops law metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults opcode ordinary byte accepted

theorem ReaderCompilerPointWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types locals data env ctx index ft st}
    (point : ReaderCompilerPointWasm2 initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
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
    ReaderCompilerPointWasm2 initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  exact state.ordinary ops law metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Exec.Code
