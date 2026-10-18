import Exec.Code.Body.Reader.Simd.ReaderSimdConstant
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Local.Lowering.Simd.SimdBitsCallbacks
import Exec.Code.Local.Lowering.Simd.SimdBits
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_simd_constant_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 12#u32 next) (C : context)
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
    after.function.simd = before.function.simd ∧
    ∃ low high values emitted,
      after.function.v128_pool.val = before.function.v128_pool.val ++ [initializerBits low high] ∧
      ReaderPostWasm2 p out.core (Wasm2.Simd.vectorConstant low high) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (Sequence.stackTypes st.core.vals.val ++ [.V128]) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (Sequence.stackTypes st.core.vals.val) (Wasm2.Simd.vectorConstant low high) [emitted]
          (Sequence.stackTypes st.core.vals.val ++ [.V128]) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,position,bits,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_constant_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_constant_callback ops before out.core low high] at callback
  rw [lower_simd_dispatch ops before out.core 524#u16 0#u32 0#u32 (initializerBits low high) reachable (by decide) (by decide)] at callback
  have ordinary := compiler_simd_ordinary_result ops law before after out.core 524#u16 0#u32 (initializerBits low high) (.Ok ()) callback
  have sources := compiler_simd_sources ops law before after out.core 524#u16 0#u32 (initializerBits low high) callback
  have cursor := compiler_simd_cursor ops law before after out.core 524#u16 0#u32 (initializerBits low high) callback
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  simp only [Wasm2.Simd.inputTypes,List.reverse_nil,List.map_nil,List.append_nil] at oldTypes
  have finalTypes : types.map Translate.valueType = Sequence.stackTypes st.core.vals.val ++ [.V128] := by
    change types.map Translate.valueType = front ++ [.V128] at newTypes
    simpa only [oldTypes] using newTypes
  obtain ⟨pool,simd,emitted,lowered,emission⟩ := compiler_simd_const_emission ops law before after out.core types C
    (Sequence.stackTypes st.core.vals.val) 0#u32 (initializerBits low high) contextLocals layout concrete finalTypes
    codeFits sourceFits coordinateFits callback
  refine ⟨ordinary,sources,cursor,simd,low,high,values,emitted,pool,post,
    ⟨lowered,SourceStack.of_map types concrete finalTypes⟩,?_⟩
  simpa only [initializerBits_val,Wasm2.Simd.vectorConstant] using emission
end Exec.Code
