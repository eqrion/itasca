import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Reader.Control.ReaderPrefixElseDormantWasm1
import Exec.Code.Body.Reader.Control.ReaderPrefixElseEnteredWasm1
import Exec.Code.Body.Reader.Control.ReaderPrefixElseDormantWasm2
import Exec.Code.Body.Reader.Control.ReaderPrefixElseEnteredWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderCompilerStateWasm1.begin_else {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry, ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.begin_else (Control.blockType savedCurrent.ctrl.block_type) condition before.function.code.val.length noEntry before.reachable)
      savedParents savedCurrent.nextElse := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_else_entered_wasm1 p ops law initial before after out types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts initialLocals entered byte accepted
    exact ⟨condition, noEntry, compiled, boundary, same, reach, fronts⟩
  | false =>
    have dead : before.reachable = false := by
      cases state.compiled.mode with
      | live _ live _ => simp [entered] at live
      | terminal dead _ _ => exact dead
      | dormant dead _ => exact dead
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_else_dormant_wasm1 p ops law initial before after out types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts entered byte accepted
    refine ⟨condition, noEntry, ?_⟩
    simpa only [dead, positionEq] using
      (⟨compiled, boundary, same, reach, fronts⟩ : ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
        parents (current.begin_else (Control.blockType savedCurrent.ctrl.block_type) condition noEntry.val noEntry false)
        savedParents savedCurrent.nextElse)

theorem ReaderCompilerStateWasm2.begin_else {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry, ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.begin_else (Wasm2.blockType savedCurrent.bt) condition before.function.code.val.length noEntry before.reachable)
      savedParents savedCurrent.nextElse := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_else_entered_wasm2 p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts initialLocals entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    exact ⟨condition, noEntry, compiled, boundary, same, reach, fronts⟩
  | false =>
    have dead : before.reachable = false := by
      cases state.compiled.mode with
      | live _ live _ => simp [entered] at live
      | terminal dead _ _ => exact dead
      | dormant dead _ => exact dead
    obtain ⟨condition, noEntry, form, positionEq, compiled, same, reach, fronts, boundary, afterState⟩ :=
      reader_prefix_else_dormant_wasm2 p ops law initial before after out ctx types functions returns locals parents current
        state.compiled state.sources state.reach state.fronts entered (by change data.val[st.core.pos.val] = 5#u8; simpa only [code.OP_ELSE] using byte) (by simpa only [code.OP_ELSE] using accepted)
    refine ⟨condition, noEntry, ?_⟩
    simpa only [dead, positionEq] using
      (⟨compiled, boundary, same, reach, fronts⟩ : ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
        parents (current.begin_else (Wasm2.blockType savedCurrent.bt) condition noEntry.val noEntry false)
        savedParents savedCurrent.nextElse)
theorem ReaderCompilerStateWasm1.else_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ReaderCompilerPointWasm1 initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨condition, noEntry, nextState⟩ := state.begin_else ops law initialLocals next advance inbounds out byte accepted
  exact nextState.point

theorem ReaderCompilerStateWasm2.else_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_ELSE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ReaderCompilerPointWasm2 initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨condition, noEntry, nextState⟩ := state.begin_else ops law initialLocals next advance inbounds out byte accepted
  exact nextState.point

end Exec.Code
