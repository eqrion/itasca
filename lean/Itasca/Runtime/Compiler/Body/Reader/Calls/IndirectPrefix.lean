import Itasca.Runtime.Compiler.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulEmission
import Itasca.Runtime.Compiler.Body.Reader.Replay.SkippedOperation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmissionTransport

/-!
A successful callback only appends pair metadata. Live reader typing supplies its operand layout; a dead callback only observes the validator state.

Main declarations: `StatefulReaderPost.indirect_prefix`. A direct consumer is `Compiler.Body.Reader.Replay.StatefulFuturePrefix`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A successful callback only appends pair metadata. Live reader typing supplies
its operand layout; a dead callback only observes the validator state. -/
theorem StatefulReaderPost.indirect_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact (post.emission ops law before after C a b arguments callback matched
      (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
      retained.layout reachable codeFits sourceFits coordinateFits).2.2.2.1
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    have frame := compiler_dead_op_frame ops law before out (statefulOpcode op) a b 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    dsimp only at frame
    refine ⟨[],?_⟩
    rw [frame]
    simp

end Itasca.Runtime.Code
