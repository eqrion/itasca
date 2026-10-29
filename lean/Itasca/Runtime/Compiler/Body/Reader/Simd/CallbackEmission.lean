import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdCallbackMeaning
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdStaticTables

/-!
SIMD constant emission and callback lowering certificates, consumed by structured reader prefixes.
-/

/-! ## Reader Simd Constant Fixed -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Callback Emission -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
