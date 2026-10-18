import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPointWithTables
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndEnteredWasm1WithTables
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndDormantWasm1WithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A non-root END closes the exact retained source scope and restores its
parent compiler point, including both entered and omitted subtrees. -/
theorem StructuredReaderCompilerStateWithTablesWasm1.end_nested {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (nonRoot : savedCurrent.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm1 jumpTables emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_entered_wasm1_with_tables p ops law initial before after out types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered nonRoot
        bodyBound byte accepted
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm1.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm1.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSourceWasm1 savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
  | false =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      dead, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_dormant_wasm1_with_tables p ops law initial before after out types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts entered bodyBound byte accepted
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm1.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm1.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSourceWasm1 savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
end Exec.Code
