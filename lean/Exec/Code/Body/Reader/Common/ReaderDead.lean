import Exec.Code.Body.Callbacks.Common.CompilerPrefixObserve
import Exec.Code.Local.Relations.Common.DeadCode
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Relations.Common.KnownPopStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.dead_op {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {types functions returns locals parents current instruction poly values}
    (post : ReaderPostWasm2 p out instruction poly values)
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (known : ConcreteStack out.vals.val)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents (current.advance instruction) out.vals.val out.pos.val ∧ after.reachable = false := by
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨invariant.dead_op ops law out instruction opcode a b bits dead known consumed accepted, ?_⟩
  have observed := compiler_op_dead ops law before out opcode a b bits dead
  rw [accepted, WP.spec_ok] at observed
  exact observed.reachable.trans dead

theorem ReaderPostWasm1.dead_op {data env ctx bt st}
    {p : Wasm1.Pending data env ctx bt st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {types functions returns locals parents current instruction poly values}
    (post : ReaderPostWasm1 p out instruction poly values)
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false) (known : ConcreteStack out.vals.val)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents (current.advance instruction) out.vals.val out.pos.val ∧ after.reachable = false := by
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨invariant.dead_op ops law out instruction opcode a b bits dead known consumed accepted, ?_⟩
  have observed := compiler_op_dead ops law before out opcode a b bits dead
  rw [accepted, WP.spec_ok] at observed
  exact observed.reachable.trans dead
end Exec.Code
