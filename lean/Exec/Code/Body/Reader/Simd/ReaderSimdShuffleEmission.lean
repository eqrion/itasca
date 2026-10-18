import Exec.Code.Body.Reader.Simd.ReaderSimdShuffleFixed
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Local.Lowering.Simd.SimdBitsCallbacks
import Exec.Code.Body.Reader.Simd.SimdReaderMeaning
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_simd_shuffle_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 13#u32 next) (C : context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ (low high : U64), ∃ front values emitted,
      after.function.simd.val = before.function.simd.val ++ [simdImmediate 13#u32 0#u32 (initializerBits low high)] ∧
      Sequence.stackTypes st.core.vals.val = front ++ [.V128,.V128] ∧
      ReaderPostWasm2 p out.core (Wasm2.Simd.shuffle low high) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ [.V128]) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ [.V128,.V128]) (Wasm2.Simd.shuffle low high) [emitted] (front ++ [.V128]) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,bits,bounds,callback,read,controls,values,effect,post⟩ := reader_simd_shuffle_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_shuffle_callback ops before out.core low high] at callback
  obtain ⟨sourceContext,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by
    simp [Control.base,ctrls,base]
  obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
  have fixed := simd_shuffle_fixed {st.core with pos := next} out.core data outer p.current.vals stack physicalBase capacity within low high read
  have retained : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits low high))
      (Wasm2.Simd.inputTypes [.V128,.V128]) (Wasm2.Simd.shuffle low high) (Wasm2.Simd.outputTypes (some .V128)) :=
    simd_shuffle_callback_meaning C low high
  obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
    reader_simd_fixed_emission p ops law before after out.core C 525#u16 13#u32 0#u32 0#u32 (initializerBits low high)
      rfl (by decide) (by decide) retained post effect fixed known monomorphic capacity contextLocals layout reachable
      codeFits sourceFits coordinateFits callback
  exact ⟨ordinary,sources,cursor,pool,low,high,front,values,emitted,simd,oldTypes,post,lowered,emission⟩
end Exec.Code
