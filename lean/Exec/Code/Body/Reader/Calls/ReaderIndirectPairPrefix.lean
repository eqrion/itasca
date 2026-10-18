import Exec.Code.Body.Reader.Calls.StructuredReaderPrefixIndirectCall
import Exec.Code.Body.Reader.Calls.StructuredReaderPrefixIndirectCallWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_indirect_call_pair_prefix_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL_INDIRECT before = .ok (.Ok (),out,after)) :
    ∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,index,values,emitted,output,pairs,reader,lowered,emission⟩ :=
      reader_emit_indirect_call_wasm1 p ops law before after out C matched
        (contextLocals.trans retained.localsEq.symm) signatures (invariant.known reachable)
        (monomorphic reachable) retained.layout reachable codeFits sourceFits coordinateFits byte accepted
    exact ⟨[(0#u32,index)],pairs⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
    obtain ⟨index,values,callback,read,reader⟩ := reader_indirect_call_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out 17#u16 index 0#u32 0#u128 = _ at callback
    have frame := compiler_dead_op_frame ops law before out 17#u16 index 0#u32 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    have pairs : after.function.indirect.val = before.function.indirect.val ++ [] := by
      dsimp only at frame
      rw [frame]; simp
    exact ⟨[],pairs⟩

theorem reader_indirect_call_pair_prefix_wasm2 {data env sourceLocals typeIndex st}
    (p : Wasm2.Pending data env sourceLocals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context)
    {emit types functions returns locals parents current}
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
    ∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra := by
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
    exact ⟨[(table,index)],pairs⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨index,table,values,callback,read,reader⟩ := reader_indirect_call_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
    have frame := compiler_dead_op_frame ops law before out.core 17#u16 index table 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    have pairs : after.function.indirect.val = before.function.indirect.val ++ [] := by
      dsimp only at frame
      rw [frame]; simp
    exact ⟨[],pairs⟩

end Exec.Code
