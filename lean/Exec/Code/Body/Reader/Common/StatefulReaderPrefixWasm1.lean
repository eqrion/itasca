import Exec.Code.Body.Reader.Common.StatefulReaderEmissionWasm1
import Exec.Code.Body.Reader.Common.ReaderStructuredDead
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StatefulReaderPostWasm1.single_prefix {data env ctx bt st}
    {p : Wasm1.Pending data env ctx bt st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPostWasm1 p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context) (pairs : List (U32 × U32))
    {types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (CumulativeEmission pairs C)
      initial before types functions returns locals parents current st.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (single : statefulUsesPair op = false) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, ReaderPostWasm1 p out op.source p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (CumulativeEmission pairs C)
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
    obtain ⟨ordinary,sources,cursor,pairEq,values,emitted,output,reader,lowered,emission⟩ :=
      post.emission ops law before after C pairs a b single arguments callback matched
        (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
        retained.layout reachable codeFits sourceFits coordinateFits
    have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := reader.span; omega
    refine ⟨values,reader,invariant.ordinary reachable ordinary lowered (.right emission)
      sources consumed (by rw [cursor]),lowered.1.2.2.2.1⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨values,reader,_⟩ := post
    have ordinary := compiler_stateful_ordinary_result ops law before after out op a b (.Ok ()) callback
    have sources := compiler_stateful_sources ops law before after out op a b callback
    have cursor := compiler_stateful_cursor ops law before after out op a b callback
    obtain ⟨compiled,deadAfter⟩ := reader.structured_skip ops law invariant dead ordinary sources cursor
      (statefulOpcode op) a b 0#u128 callback
    exact ⟨values,reader,compiled,deadAfter.trans dead.symm⟩

end Exec.Code
