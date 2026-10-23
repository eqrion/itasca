import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_simd_constant_fixed_emission {data env locals index st values position}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (a b : U32) (bits : U128)
    (post : ReaderPostWasm2 p out (.VCONST .V128 (.mk_uN bits.val)) p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [] (some .V128) values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} [] (some .V128) = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out 524#u16 a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
    after.function.simd = before.function.simd ∧ after.function.v128_pool.val = before.function.v128_pool.val ++ [bits] ∧
    ∃ emitted, TypedLowered before after out.vals.val emitted (Sequence.stackTypes st.core.vals.val ++ [.V128]) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (Sequence.stackTypes st.core.vals.val) (.VCONST .V128 (.mk_uN bits.val)) [emitted]
          (Sequence.stackTypes st.core.vals.val ++ [.V128]) := by
  rw [lower_simd_dispatch ops before out 524#u16 a b bits reachable (by decide) (by decide)] at accepted
  have ordinary := compiler_simd_ordinary_result ops law before after out 524#u16 a bits (.Ok ()) accepted
  have sources := compiler_simd_sources ops law before after out 524#u16 a bits accepted
  have cursor := compiler_simd_cursor ops law before after out 524#u16 a bits accepted
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  simp only [Wasm2.Simd.inputTypes,List.reverse_nil,List.map_nil,List.append_nil] at oldTypes
  have finalTypes : types.map Translate.valueType = Sequence.stackTypes st.core.vals.val ++ [.V128] := by
    change types.map Translate.valueType = front ++ [.V128] at newTypes
    simpa only [oldTypes] using newTypes
  obtain ⟨pool,simd,emitted,lowered,emission⟩ := compiler_simd_const_emission ops law before after out types C
    (Sequence.stackTypes st.core.vals.val) a bits contextLocals layout concrete finalTypes
    codeFits sourceFits coordinateFits accepted
  exact ⟨ordinary,sources,cursor,simd,pool,emitted,⟨lowered,SourceStack.of_map types concrete finalTypes⟩,emission⟩
end Exec.Code
