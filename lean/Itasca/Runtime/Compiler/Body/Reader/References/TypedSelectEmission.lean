import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdLane
import Itasca.Wasm2.References.Step
import Itasca.Wasm2.References.Reader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdTypes
import Itasca.Runtime.Compiler.Local.Source.SourceEntry
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Sections, each formerly its own module: TypedSelect, StatefulReferences, TypedSelectEmission.
-/

/-! ## TypedSelect -/

section

/-!
The explicit-select reader retains its literal declared type, exact callback, validated stack effect, and independently decoded source prefix.

Main declarations: `reader_typed_select_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

/-- The explicit-select reader retains its literal declared type, exact
callback, validated stack effect, and independently decoded source prefix. -/
theorem reader_typed_select_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile visitor st data env ctx index 28#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ ty position, visitor.on_select_typed before out.core ty = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [.I32,ty,ty] (some ty) =
        .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [.I32,ty,ty] (some ty) values ∧
        Wasm2.ReaderPost p out.core (.SELECT (some [Translate.valueType ty])) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 28#u8 before after (by decide) accepted
  rw [code.step_wasm2.typed_select] at run
  obtain ⟨selected,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  rw [code.read_typed_select.fixed] at read
  obtain ⟨⟨reply,parsed⟩,decode,values,controls,typeInfo⟩ := WP.spec_imp_exists (Wasm2.selectType.spec st.core data)
  dsimp only at values controls typeInfo
  cases reply with
  | Err error => simp [Wasm2.metadataOperands,decode] at read
  | Ok ty =>
    simp only [Wasm2.metadataOperands,decode,bind_ok] at read
    obtain ⟨⟨result,checked⟩,fixed,final⟩ := bind_ok_inv _ _ _ read
    cases result with
    | Err error => simp [uncurry_apply_pair] at final
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,id_eq,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at final
      obtain ⟨rfl,rfl⟩ := final
      have parsedEq : parsed = {st.core with pos := parsed.pos} := Wasm2.Simd.state_of_stacks parsed st.core values controls
      rw [parsedEq] at fixed
      obtain ⟨count,bytes,encoding⟩ := typeInfo ty rfl
      have encoded : Wasm2.At data p.start (.plain (.SELECT (some [Translate.valueType ty]))) parsed.pos :=
        Wasm2.At.of_immediate p.inbounds byte p.pos (.reference (.selectTyped ty encoding)) bytes
      refine ⟨ty,parsed.pos,callback,fixed,?_⟩
      exact Wasm2.Pending.fixed_reader_accepted p parsed.pos out.core _ _ _ capacity (.instr_case_3 _)
        (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices])
        (fun C wf _ => by simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType]
          using Instr_ok.select_expl C (Translate.valueType ty) wf (.instr_case_3 _)) encoded fixed

end Itasca.Runtime.Compiler

end

/-! ## StatefulReferences -/

section

/-!
Reference-reader inversion and stateful postconditions for ref.func and ref.is_null, retaining the declared-reference obligation.
-/

/-! ## Reader Reference Steps -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_ref_func_wasm2 {data env locals index st}
    (p : Pending data env locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    idx.val < env.func_types.val.length ∧ out.ctrls = st.core.ctrls ∧
      out.vals.val = st.core.vals.val ++ [.Val .FuncRef] ∧
      Wasm2.ReaderPost p out (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .FuncRef]) := by
  have effect := p.ref_func_reader byte size
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨bound, controls, values, post, _⟩ := effect idx rfl
  exact ⟨bound, controls, values, post⟩

theorem reader_ref_is_null_wasm2 {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ rt values, Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [ModuleConstants.referenceValueType rt] (some .I32) values ∧
        Wasm2.ReaderPost p out .REF_IS_NULL p.current.ctrl.polymorphic_base values := by
  have effect := p.ref_is_null_reader byte size
  rw [accepted, WP.spec_ok] at effect
  exact ⟨effect.1, effect.2.1, effect.2.2 rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Stateful Reader References -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

private theorem fixed_effect_concrete {before after inputs output}
    (known : ConcreteStack before) (effect : Simd.FixedEffect false before inputs output after) :
    ConcreteStack after := by
  obtain ⟨front,afterTypes,beforeRealized⟩ := effect _ (Sequence.realizes_default false after)
  have beforeConcrete := concrete_realization known beforeRealized
  apply stack_types_concrete
  rw [afterTypes]
  intro member
  rcases List.mem_append.mp member with member | member
  · exact beforeConcrete (List.mem_append_left _ member)
  · cases output with
    | none => simp [Simd.outputTypes] at member
    | some ty => cases ty <;> simp [Simd.outputTypes,Translate.valueType] at member

/-- Reference tests derive their concrete live suffix from the canonical fixed
effect; dead polymorphic paths only retain the exact source zipper. -/
theorem reader_ref_is_null_post_wasm2 {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    StatefulReaderPost p out .refIsNull := by
  obtain ⟨controls,position,rt,values,effect,post⟩ := reader_ref_is_null_wasm2 p out byte size accepted
  refine ⟨values,post,?_⟩
  intro C matched known monomorphic
  obtain ⟨sourceC,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  obtain ⟨outerKnown,currentKnown⟩ := concrete_stack_append.mp (stack ▸ known)
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  have afterKnown := fixed_effect_concrete currentKnown effect
  obtain ⟨C',outer',spine',header',base',typed',ctrls',blocks',stack'⟩ := post.opened
  have outerEq : outer' = outer := (wasm2_spine_values spine').trans (wasm2_spine_values spine).symm
  refine ⟨Sequence.stackTypes outer ++ front,Simd.inputTypes [ModuleConstants.referenceValueType rt],
    Simd.outputTypes (some .I32),?_,?_,?_,?_⟩
  · simpa [Simd.inputTypes,Simd.outputTypes,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.map_cons,List.map_nil,reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using
      SourceMachine.Stateful.Signature.refIsNull (C := C) (Translate.referenceType rt)
  · simp only [stack,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes values = _
    rw [afterTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance]
    exact concrete_stack_append.mpr ⟨outerKnown,afterKnown⟩

theorem reader_ref_func_post_wasm2 {data env locals index st}
    (p : Pending data env locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    StatefulReaderPost p out (.refFunc idx.val) := by
  obtain ⟨bound,controls,values,post⟩ := reader_ref_func_wasm2 p idx out byte size accepted
  refine ⟨_,post,?_⟩
  intro C matched known _
  refine ⟨Sequence.stackTypes st.core.vals.val,[],[valtype.FUNCREF],?_,by simp,?_,?_⟩
  · apply SourceMachine.Stateful.Signature.refFunc idx.val (EnvTranslation.funcType env.func_types.val[idx.val])
    simp [matched.funcs,List.getElem?_eq_getElem bound]
  · simp [values,Sequence.stackTypes,Translate.valueType]
  · rw [values]
    exact concrete_stack_append.mpr ⟨known,by simp [ConcreteStack]⟩

end Itasca.Runtime.Compiler

end

end

/-! ## TypedSelectEmission -/

section

/-!
Accepted explicit-select bytes and their actual callback produce the typed emission and exact complete stack transition used by body compilation.

Main declarations: `reader_emit_typed_select_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.TypedSelectCheckedPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Accepted explicit-select bytes and their actual callback produce the typed
emission and exact complete stack transition used by body compilation. -/
theorem reader_emit_typed_select_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (ty : wasm_types.ValueType) (front : List valtype) (values : List code.StackType) (emitted : runtime.bytecode.Instr),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty,Translate.valueType ty,.I32] ∧
      Wasm2.ReaderPost p out.core (.SELECT (some [Translate.valueType ty])) p.current.ctrl.polymorphic_base values ∧
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

end Itasca.Runtime.Compiler

end
