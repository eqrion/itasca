import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Simd.StructuredSimdEmbedding
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Body.Reader.Table.ReaderStructuredDead
import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.simd_dead_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current source poly values}
    (post : ReaderPostWasm2 p out source poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance source)
      out.vals.val out.pos.val ∧ after.reachable = false ∧
      CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  obtain ⟨ordinary,sources,cursor,capacity⟩ := compiler_lower_simd_effects ops law before after out opcode a b bits lower upper accepted
  obtain ⟨prefixProof,deadAfter⟩ := post.structured_skip ops law invariant dead ordinary sources cursor opcode a b bits accepted
  unfold runtime.compiler.lower.FunctionCompiler.op at accepted
  rw [if_neg (by simp [dead])] at accepted
  exact ⟨prefixProof,deadAfter,compiler_observe_tables ops law before after out (.Ok ()) accepted⟩
end Itasca.Runtime.Code
