import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixObserve
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack

/-!
Dormant structured prefixes for omitted source operations.

Main declarations: `ReaderPostWasm2.structured_dead_op`. A direct consumer is `Compiler.Body.Reader.Calls.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.structured_dead_op {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current instruction poly values}
    (post : ReaderPostWasm2 p out instruction poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) out.vals.val out.pos.val ∧ after.reachable = false := by
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨invariant.dead_op ops law out instruction opcode a b bits dead consumed accepted, ?_⟩
  have observed := compiler_op_dead ops law before out opcode a b bits dead
  rw [accepted, WP.spec_ok] at observed
  exact observed.reachable.trans dead

end Itasca.Runtime.Compiler
