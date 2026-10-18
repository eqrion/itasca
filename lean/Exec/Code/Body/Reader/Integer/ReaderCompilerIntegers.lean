import Exec.Code.Body.Reader.Common.ReaderCompilerState
import Exec.Code.Body.Reader.Integer.ReaderPrefixInteger
import Exec.Code.Body.Reader.Integer.ReaderPrefixDeadInteger
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderCompilerStateWasm2.integer {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (ty : Inn) (op : IntegerBinary) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (binaryOpcode ty op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ values, ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (op.source ty)) savedParents
      (savedCurrent.advance (.plain (op.source ty)) (op.source ty)
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_integer_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach (state.reach.current reach) ty op sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post (by cases op <;> simp [IntegerBinary.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_integer_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach ty op byte accepted
    exact ⟨values, state.advance next advance inbounds post (by cases op <;> simp [IntegerBinary.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm1.integer {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (ty : Inn) (op : IntegerBinary) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = (UScalar.cast .U8 (binaryOpcode ty op)))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx (UScalar.cast .U8 (binaryOpcode ty op)) before = .ok (.Ok (), out, after)) :
    ∃ values, ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (op.source ty)) savedParents
      (savedCurrent.advance (.plain (op.source ty)) (op.source ty)
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_integer_wasm1 p ops law initial before after out
      state.compiled reach (state.reach.current reach) ty op sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_integer_wasm1 p ops law initial before after out
      state.compiled reach ty op byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (by simp [dead])⟩
theorem ReaderCompilerStateWasm2.eqz {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (ty : Inn) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (eqzOpcode ty)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    ∃ values, ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (eqzSource ty)) savedParents
      (savedCurrent.advance (.plain (eqzSource ty)) (eqzSource ty)
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_eqz_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach (state.reach.current reach) ty sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [eqzSource, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_eqz_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach ty byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [eqzSource, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm1.eqz {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (ty : Inn) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = (UScalar.cast .U8 (eqzOpcode ty)))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    ∃ values, ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (eqzSource ty)) savedParents
      (savedCurrent.advance (.plain (eqzSource ty)) (eqzSource ty)
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_eqz_wasm1 p ops law initial before after out
      state.compiled reach (state.reach.current reach) ty sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_eqz_wasm1 p ops law initial before after out
      state.compiled reach ty byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (by simp [dead])⟩
end Exec.Code
