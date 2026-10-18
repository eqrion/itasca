import Exec.Code.Local.Control.Simd.StructuredSimdEmbedding
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Body.Reader.Common.ReaderStructuredDead
import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.simd_live_prefix {data env sourceLocals index st source values position inputs output}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    (C : context) {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits)
      (Wasm2.Simd.inputTypes inputs) source (Wasm2.Simd.outputTypes output))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance source)
      out.vals.val out.pos.val := by
  obtain ⟨entered,retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
    reader_simd_fixed_emission p ops law before after out C opcode sub a b bits number bounded nonconstant
      meaning post effect read (invariant.known reachable) monomorphic capacity (contextLocals.trans retained.localsEq.symm)
      retained.layout reachable codeFits sourceFits coordinateFits accepted
  have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
  apply invariant.ordinary reachable ordinary lowered _ sources consumed (by rw [cursor])
  simpa only [oldTypes] using (SimdEmbedding.lift (emit := emit) emission)

theorem ReaderPostWasm2.simd_dead_prefix {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current source poly values}
    (post : ReaderPostWasm2 p out source poly values)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance source)
      out.vals.val out.pos.val ∧ after.reachable = false ∧
      CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  obtain ⟨ordinary,sources,cursor,capacity⟩ := compiler_lower_simd_effects ops law before after out opcode a b bits lower upper accepted
  obtain ⟨prefixProof,deadAfter⟩ := post.structured_skip ops law invariant dead ordinary sources cursor opcode a b bits accepted
  unfold runtime.compiler.lower.FunctionCompiler.op at accepted
  rw [if_neg (by simp [dead])] at accepted
  exact ⟨prefixProof,deadAfter,compiler_observe_tables ops law before after out (.Ok ()) accepted⟩
end Exec.Code
