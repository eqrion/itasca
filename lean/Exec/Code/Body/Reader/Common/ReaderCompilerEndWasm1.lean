import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Reader.Common.ReaderPrefixEndEnteredWasm1
import Exec.Code.Body.Reader.Common.ReaderPrefixEndDormantWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A non-root END closes the exact retained source scope and restores its
parent compiler point, including both entered and omitted subtrees. -/
theorem ReaderCompilerStateWasm1.end_nested {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (nonRoot : savedCurrent.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    ReaderCompilerPointWasm1 initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_end_entered_wasm1 p ops law initial before after out types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts initialLocals entered nonRoot
        bodyBound byte accepted
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSourceWasm1 savedParent p.current instruction,
      compiled, boundary, same, reach, fronts⟩
  | false =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      dead, compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_end_dormant_wasm1 p ops law initial before after out types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts entered bodyBound byte accepted
    exact ⟨outer, parent.advance instruction, savedOuter, resumedSourceWasm1 savedParent p.current instruction,
      compiled, boundary, same, reach, fronts⟩
end Exec.Code
