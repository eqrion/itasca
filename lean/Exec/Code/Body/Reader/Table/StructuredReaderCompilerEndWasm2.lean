import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndEnteredWasm2
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndDormantWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A non-root END closes the exact retained source scope and restores its
parent compiler point, including both entered and omitted subtrees. -/
theorem StructuredReaderCompilerStateWasm2.end_nested {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (typesEq : types = env.types.val.map EnvTranslation.funcType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (nonRoot : savedCurrent.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_END)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_END before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_entered_wasm2 p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered typesEq nonRoot
        bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
  | false =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      dead, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_dormant_wasm2 p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts entered bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
end Exec.Code
