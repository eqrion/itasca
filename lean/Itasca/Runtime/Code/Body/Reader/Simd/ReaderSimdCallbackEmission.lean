import Itasca.Runtime.Code.Body.Lowering.Simd.SimdCallbackMeaning
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdConstantFixed
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdStaticTables
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Every independently classified SIMD callback yields typed emitted code
and an exact append to the four syntactic function tables. -/
theorem reader_simd_callback_emission {data env locals index st source values position inputs output}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val)
    (meaning : SimdCallbackMeaning C sub a bits inputs source output)
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
    ∃ extra front emitted,
      CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      TypedLowered before after out.vals.val emitted (front ++ Wasm2.Simd.outputTypes output) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ Wasm2.Simd.inputTypes inputs) source [emitted] (front ++ Wasm2.Simd.outputTypes output) := by
  have bounded := meaning.opcode_bound
  obtain ⟨indirect,jumps⟩ := compiler_lower_simd_preserved_tables ops law before after out opcode a b bits (by omega) (by omega) accepted
  cases meaning with
  | instruction meaning =>
    obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
      reader_simd_fixed_emission p ops law before after out C opcode sub a b bits number bounded meaning.not_constant
        meaning post effect read known monomorphic capacity contextLocals layout reachable codeFits sourceFits coordinateFits accepted
    refine ⟨ordinary,sources,cursor,⟨[],[simdImmediate sub a bits],[],[]⟩,front,emitted,?_,oldTypes,lowered,emission⟩
    simp only [CompilerTables.ofFunction,CompilerTables.append,indirect,jumps,simd,pool,List.append_nil]
  | constant a bits =>
    have opcodeEq : opcode = 524#u16 := by scalar_tac
    subst opcode
    obtain ⟨ordinary,sources,cursor,simd,pool,emitted,lowered,emission⟩ :=
      reader_simd_constant_fixed_emission p ops law before after out C a b bits post effect read known monomorphic
        capacity contextLocals layout reachable codeFits sourceFits coordinateFits accepted
    refine ⟨ordinary,sources,cursor,⟨[],[],[bits],[]⟩,Sequence.stackTypes st.core.vals.val,emitted,?_,?_,lowered,?_⟩
    · simp only [CompilerTables.ofFunction,CompilerTables.append,indirect,jumps,simd,pool,List.append_nil]
    · simp [Wasm2.Simd.inputTypes]
    · simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType] using emission
end Itasca.Runtime.Code
