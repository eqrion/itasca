import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Common.ReaderTypedSelectEmission
import Exec.Code.Body.Reader.Table.ReaderStructuredDead
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.typed_select {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit}
    (embedding : ∀ {input instruction code output}, TypedSelectEmission C input instruction code output → emit input instruction code output)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨entered,retained⟩ := state.compiled.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := state.compiled.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := state.compiled.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,ty,front,values,emitted,input,post,lowered,emission⟩ :=
      reader_emit_typed_select_wasm2 p ops law before after out ctx C
        (contextLocals.trans retained.localsEq.symm).symm (state.compiled.known live) (state.reach.current live)
        retained.layout live codeFits sourceFits coordinateFits byte accepted
    have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
    have compiled := state.compiled.ordinary live ordinary lowered (input ▸ embedding emission) sources consumed (by rw [cursor])
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨ty,position,callback,read,controls,cursor,values,effect,post⟩ := reader_typed_select_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
    obtain ⟨compiled,dead⟩ := post.structured_skip ops law state.compiled live
      (compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback)
      (compiler_core_sources ops law before after out.core (.select true) callback)
      (compiler_core_cursor ops law before after out.core (.select true) callback)
      28#u16 0#u32 0#u32 0#u128 callback
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point
end Exec.Code
