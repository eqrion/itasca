import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdTypes
import Itasca.Runtime.Compiler.Local.Source.TypedSelectLowering
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Accepted explicit-select bytes and their actual callback produce the typed emission and exact complete stack transition used by body compilation.

Main declarations: `reader_emit_typed_select_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.TypedSelectCheckedPrefix`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Accepted explicit-select bytes and their actual callback produce the typed
emission and exact complete stack transition used by body compilation. -/
theorem reader_emit_typed_select_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (ty : types.ValueType) (front : List valtype) (values : List code.StackType) (emitted : runtime.bytecode.Instr),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty,Translate.valueType ty,.I32] ∧
      ReaderPostWasm2 p out.core (.SELECT (some [Translate.valueType ty])) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ [Translate.valueType ty]) ∧
      TypedSelectEmission C (front ++ [Translate.valueType ty,Translate.valueType ty,.I32])
        (.SELECT (some [Translate.valueType ty])) [emitted] (front ++ [Translate.valueType ty]) := by
  obtain ⟨capacity,_⟩ := profile_scalar_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index 28#u8 before after (by decide) accepted
  obtain ⟨ty,position,callback,read,controls,cursor,values,effect,post⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨front,types,beforeTypes,concrete,output⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  simp only [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,List.reverse_cons,List.reverse_nil,
    List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,Translate.valueType] at beforeTypes output
  rw [beforeTypes] at layout
  have lowered := compiler_typed_select_emission ops law before out.core types C front (Translate.valueType ty)
    localsMatch layout reachable concrete output codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select true) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select true) callback
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨ordinary,sources,cursor,ty,front,values,emitted,beforeTypes,post,
    ⟨lower,SourceStack.of_map types concrete output⟩,emission⟩

end Itasca.Runtime.Code
