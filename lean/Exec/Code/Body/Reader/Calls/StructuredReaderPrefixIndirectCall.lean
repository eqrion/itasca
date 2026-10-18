import Exec.Code.Body.Reader.Calls.ReaderIndirectEmission
import Exec.Code.Body.Reader.Common.ReaderStructuredDead
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A fixed future pair table suffices for both sides of indirect-call lowering.
Dead paths retain the exact reader advance without requiring concrete operands. -/
theorem structured_reader_prefix_indirect_call_wasm2 {data env sourceLocals typeIndex st}
    (p : Wasm2.Pending data env sourceLocals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (future : List (U32 × U32))
    {emit types functions returns locals parents current}
    (embedding : ∀ input instruction emitted output,
      IndirectCallEmission (after.function.indirect.val ++ future) C input instruction emitted output →
        emit input instruction emitted output)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    ∃ (index table : U32) (values : List code.StackType) (extra : List (U32 × U32)),
      after.function.indirect.val = before.function.indirect.val ++ extra ∧
      ReaderPostWasm2 p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.advance (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val))) out.core.vals.val out.core.pos.val ∧
      after.reachable = before.reachable := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,index,table,values,emitted,output,pairs,reader,lowered,emission⟩ :=
      reader_emit_indirect_call_wasm2 p ops law before after out ctx C matched
        (contextLocals.trans retained.localsEq.symm) signatures (invariant.known reachable)
        (monomorphic reachable) retained.layout reachable codeFits sourceFits coordinateFits byte accepted
    have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := reader.span; omega
    exact ⟨index,table,values,[(table,index)],pairs,reader,
      invariant.ordinary reachable ordinary lowered (embedding _ _ _ _ (emission.append_pairs future))
        sources consumed (by rw [cursor]),lowered.1.2.2.2.1⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨index,table,values,callback,read,reader⟩ := reader_indirect_call_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
    have frame := compiler_dead_op_frame ops law before out.core 17#u16 index table 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    have pairs : after.function.indirect.val = before.function.indirect.val ++ [] := by
      dsimp only at frame
      rw [frame]; simp
    obtain ⟨compiled,deadAfter⟩ := reader.structured_skip ops law invariant dead
      (compiler_indirect_call_ordinary_result ops law before after out.core index table (.Ok ()) callback)
      (compiler_indirect_call_sources ops law before after out.core index table callback)
      (compiler_indirect_call_cursor ops law before after out.core index table callback)
      17#u16 index table 0#u128 callback
    exact ⟨index,table,values,[],pairs,reader,compiled,deadAfter.trans dead.symm⟩
end Exec.Code
