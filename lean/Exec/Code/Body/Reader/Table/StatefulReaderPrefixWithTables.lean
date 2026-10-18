import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Body.Reader.Common.StatefulReaderEmission
import Exec.Code.Body.Reader.Table.ReaderStructuredDeadWithTables
import Exec.Code.Local.Relations.Common.StatefulEmissionTransport
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A successful callback only appends pair metadata. Live reader typing supplies
its operand layout; a dead callback only observes the validator state. -/
theorem StatefulReaderPost.indirect_prefix_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
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

/-- A fixed future metadata table can be used on both sides of one actual
stateful callback. Its current entries are retained by list append. -/
theorem StatefulReaderPost.future_prefix_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context) (future : List (U32 × U32))
    {types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) (CumulativeEmission (after.function.indirect.val ++ future) C)
      initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) (CumulativeEmission (after.function.indirect.val ++ future) C)
        initial after types functions returns locals parents (current.advance op.source) out.vals.val out.pos.val ∧
      after.reachable = before.reachable := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,pairs,values,emitted,output,reader,lowered,emission⟩ :=
      post.emission ops law before after C a b arguments callback matched
        (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
        retained.layout reachable codeFits sourceFits coordinateFits
    have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := reader.span; omega
    refine ⟨values,reader,invariant.ordinary reachable ordinary lowered (.right (emission.map_pairs ?_))
      sources consumed (by rw [cursor]) emission.not_branchTable,lowered.1.2.2.2.1⟩
    intro index pair found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simpa only [List.getElem?_append,if_pos bound] using found
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨values,reader,_⟩ := post
    have ordinary := compiler_stateful_ordinary_result ops law before after out op a b (.Ok ()) callback
    have sources := compiler_stateful_sources ops law before after out op a b callback
    have cursor := compiler_stateful_cursor ops law before after out op a b callback
    obtain ⟨compiled,deadAfter⟩ := reader.structured_skip_with_tables ops law invariant dead ordinary sources cursor
      (statefulOpcode op) a b 0#u128 callback
    exact ⟨values,reader,compiled,deadAfter.trans dead.symm⟩

end Exec.Code
