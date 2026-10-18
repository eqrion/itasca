import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerEnterBlock
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerEnterLoop
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerEnterIf
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerBranches
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerPointWasm1.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st}
    (point : StructuredReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h
  · have op : opcode = 2#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.enter_block ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 3#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.enter_loop ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 4#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, post⟩ := state.enter_if ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 12#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, post⟩ := state.br ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 13#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.br_if ops law next advance inbounds out sourceBound
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point

theorem StructuredReaderCompilerPointWasm2.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : StructuredReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h
  · have op : opcode = 2#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_block ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 3#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_loop ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 4#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, post⟩ := state.enter_if ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 12#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, post⟩ := state.br ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 13#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.br_if ops law next advance inbounds out sourceBound
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
end Exec.Code
