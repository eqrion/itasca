import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Body.Reader.Simd.ReaderPrefixSimd
import Exec.Code.Body.Reader.Simd.ReaderSimdCallbackEmission
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The complete SIMD prefix step handles live emission and polymorphic dead
code, retaining an exact append witness for all function tables. -/
theorem ReaderPostWasm2.simd_callback_prefix {jumpTables : List U32} {data env sourceLocals index st source values position inputs output}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    (C : context) {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val)
    (meaning : SimdCallbackMeaning C sub a bits inputs source output)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance source)
        out.vals.val out.pos.val ∧
      (after.reachable = true → p.current.ctrl.polymorphic_base = false) := by
  cases reachable : before.reachable with
  | false =>
    have bound := meaning.opcode_bound
    obtain ⟨prefixProof,dead,tables⟩ := post.simd_dead_prefix ops law invariant reachable opcode a b bits
      (by omega) (by omega) accepted
    refine ⟨CompilerTables.empty,?_,prefixProof,by simp [dead]⟩
    simpa only [CompilerTables.append_empty] using tables
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C opcode sub a b bits number meaning post effect read
        (invariant.known reachable) (monomorphic reachable) capacity (contextLocals.trans retained.localsEq.symm)
        retained.layout reachable codeFits sourceFits coordinateFits accepted
    have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
    refine ⟨extra,tables,?_,fun _ => monomorphic reachable⟩
    apply invariant.ordinary reachable ordinary lowered _ sources consumed (by rw [cursor]) emission.not_branchTable
    simpa only [oldTypes] using (SimdEmbedding.lift (emit := emit) emission)
end Itasca.Runtime.Code
