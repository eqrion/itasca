import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdTypes
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdEffects
import Itasca.Runtime.Code.Body.Source.TypedLowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Canonical SIMD reader effects and the actual accepted callback produce
exact typed emitted-code evidence, including appended metadata. -/
theorem reader_simd_fixed_emission {data env locals index st source values position inputs output}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits)
      (Wasm2.Simd.inputTypes inputs) source (Wasm2.Simd.outputTypes output))
    (post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
    after.function.simd.val = before.function.simd.val ++ [simdImmediate sub a bits] ∧
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ front emitted, Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      TypedLowered before after out.vals.val emitted (front ++ Wasm2.Simd.outputTypes output) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ Wasm2.Simd.inputTypes inputs) source [emitted] (front ++ Wasm2.Simd.outputTypes output) := by
  rw [lower_simd_dispatch ops before out opcode a b bits reachable (by omega) (by omega)] at accepted
  have ordinary := compiler_simd_ordinary_result ops law before after out opcode a bits (.Ok ()) accepted
  have sources := compiler_simd_sources ops law before after out opcode a bits accepted
  have cursor := compiler_simd_cursor ops law before after out opcode a bits accepted
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  rw [oldTypes] at layout
  obtain ⟨simd,pool,emitted,lowered,emission⟩ := compiler_simd_emission ops law before after out types C front _ _ source
    opcode sub a bits number bounded nonconstant meaning contextLocals layout concrete newTypes
    codeFits sourceFits coordinateFits accepted
  exact ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,
    ⟨lowered,SourceStack.of_map types concrete newTypes⟩,emission⟩
end Itasca.Runtime.Code
