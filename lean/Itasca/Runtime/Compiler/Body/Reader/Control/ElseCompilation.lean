import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint
import Itasca.Runtime.Compiler.Body.Reader.Control.ElseDormantWasm2Prefix
import Itasca.Runtime.Compiler.Body.Reader.Control.ElseEnteredPrefix

/-!
Else-entry compilation through a structured reader state.

Main declarations: `StructuredReaderCompilerStateWasm2.begin_else` and `StructuredReaderCompilerStateWasm2.else_`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.begin_else {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.begin_else (Wasm2.blockType savedCurrent.bt) condition before.function.code.val.length noEntry before.reachable)
      savedParents savedCurrent.nextElse := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_else_entered_wasm2 p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    exact ⟨condition, noEntry, compiled, boundary, same, reach, fronts, state.knownFronts.begin_else _ condition _ noEntry _⟩
  | false =>
    have dead : before.reachable = false := by
      cases state.compiled.mode with
      | live _ live _ => simp [entered] at live
      | terminal dead _ _ => exact dead
      | dormant dead _ => exact dead
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_else_dormant_wasm2 p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    refine ⟨condition, noEntry, ?_⟩
    simpa only [dead, positionEq] using
      (⟨compiled, boundary, same, reach, fronts, state.knownFronts.begin_else _ condition _ noEntry _⟩ : StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
        parents (current.begin_else (Wasm2.blockType savedCurrent.bt) condition noEntry.val noEntry false)
        savedParents savedCurrent.nextElse)
theorem StructuredReaderCompilerStateWasm2.else_ {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_ELSE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨condition, noEntry, nextState⟩ := state.begin_else ops law initialLocals next advance inbounds out byte accepted
  exact nextState.point

end Itasca.Runtime.Compiler
