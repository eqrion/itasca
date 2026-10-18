import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Reader.Control.ReaderCompilerEnterBlock
import Exec.Code.Body.Reader.Control.ReaderCompilerEnterLoop
import Exec.Code.Body.Reader.Control.ReaderCompilerEnterIf
import Exec.Code.Body.Reader.Control.ReaderCompilerBranches
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Opening a structured scope and branching preserve a retained exact reader
point. Closing delimiters are handled separately because root END completes it. -/
def ScopeOpcode (opcode : U8) : Prop := opcode.val ∈ [2, 3, 4, 12, 13]

theorem ReaderCompilerPointWasm1.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st}
    (point : ReaderCompilerPointWasm1 initial before types functions returns locals data env ctx bodyBt st)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    ReaderCompilerPointWasm1 initial after types functions returns locals data env ctx bodyBt out := by
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

theorem ReaderCompilerPointWasm2.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (point : ReaderCompilerPointWasm2 initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    ReaderCompilerPointWasm2 initial after types functions returns locals data env ctx.locals index ft out := by
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
