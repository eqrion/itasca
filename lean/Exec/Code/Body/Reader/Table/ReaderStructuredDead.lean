import Exec.Code.Body.Control.Table.StructuredPrefixDead
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.structured_skip {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current instruction poly values}
    (post : ReaderPostWasm2 p out instruction poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (ordinary : CompilerOrdinaryStable before after) (sources : SourceProgress before after)
    (cursor : after.next_source = out.pos)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val ∧ after.reachable = false := by
  have effect := compiler_dead_op_fields ops law before out opcode a b bits dead
  rw [accepted,WP.spec_ok] at effect
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨invariant.skip instruction dead effect.2.2.2 ordinary effect.1 sources consumed (by rw [cursor]),effect.2.2.2⟩
end Exec.Code
