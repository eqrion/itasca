import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Body.References.Reader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulMetadataPosts
import Itasca.Runtime.Compiler.Local.Source.InstructionSourceAndEntry
import Itasca.Runtime.Compiler.Local.Relations.LoweringEffects
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState

/-!
Proofs for Runtime / Compiler / Body / Reader / References.

This module collects TypedSelectEmission, StructuredCompilerTypedSelect.
Each section documents its contracts and consumers.
-/

/-! ## TypedSelectEmission -/

section

/-! ## TypedSelect -/

section

/-!
The explicit-select reader retains its literal declared type, exact callback, validated stack effect, and independently decoded source prefix.

Main declarations: `reader_typed_select`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation

/-- The explicit-select reader retains its literal declared type, exact
callback, validated stack effect, and independently decoded source prefix. -/
theorem reader_typed_select {data env locals index st}
    (p : Body.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile visitor st data env ctx index 28#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ ty position, visitor.on_select_typed before out.core ty = .ok (.Ok (),after) ∧
      Body.Simd.readFixed {st.core with pos := position} [.I32,ty,ty] (some ty) =
        .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Body.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [.I32,ty,ty] (some ty) values ∧
        Body.ReaderPost p out.core (.SELECT (some [Translation.valueType ty])) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := scalar_success visitor st out data env ctx index 28#u8 before after (by decide) accepted
  rw [code.step_wasm2.typed_select] at run
  obtain ⟨selected,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
  rw [code.read_typed_select.fixed] at read
  obtain ⟨⟨reply,parsed⟩,decode,values,controls,typeInfo⟩ := WP.spec_imp_exists (Body.selectType.spec st.core data)
  dsimp only at values controls typeInfo
  cases reply with
  | Err error => simp [Body.metadataOperands,decode] at read
  | Ok ty =>
    simp only [Body.metadataOperands,decode,bind_ok] at read
    obtain ⟨⟨result,checked⟩,fixed,final⟩ := bind_ok_inv _ _ _ read
    cases result with
    | Err error => simp [uncurry_apply_pair] at final
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,id_eq,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at final
      obtain ⟨rfl,rfl⟩ := final
      have parsedEq : parsed = {st.core with pos := parsed.pos} := Body.Simd.state_of_stacks parsed st.core values controls
      rw [parsedEq] at fixed
      obtain ⟨count,bytes,encoding⟩ := typeInfo ty rfl
      have encoded : Body.At data p.start (.plain (.SELECT (some [Translation.valueType ty]))) parsed.pos :=
        Body.At.of_immediate p.inbounds byte p.pos (.reference (.selectTyped ty encoding)) bytes
      refine ⟨ty,parsed.pos,callback,fixed,?_⟩
      exact Body.Pending.fixed_reader_accepted p parsed.pos out.core _ _ _ capacity (.instr_case_3 _)
        (by simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices])
        (fun C wf _ => by simpa [Body.Simd.inputTypes,Body.Simd.outputTypes,Translation.valueType]
          using Instr_ok.select_expl C (Translation.valueType ty) wf (.instr_case_3 _)) encoded fixed

end Itasca.Compiler

end

/-! ## StatefulReferences -/

section

/-!
Reference-reader inversion and stateful postconditions for ref.func and ref.is_null, retaining the declared-reference obligation.
-/

/-! ## Reader Reference Steps -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem reader_ref_func {data env locals index st}
    (p : Pending data env locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    idx.val < env.func_types.val.length ∧ out.ctrls = st.core.ctrls ∧
      out.vals.val = st.core.vals.val ++ [.Val .FuncRef] ∧
      Body.ReaderPost p out (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .FuncRef]) := by
  have effect := p.ref_func_reader byte size
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨bound, controls, values, post, _⟩ := effect idx rfl
  exact ⟨bound, controls, values, post⟩

theorem reader_ref_is_null {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ rt values, Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [Module.Constants.referenceValueType rt] (some .I32) values ∧
        Body.ReaderPost p out .REF_IS_NULL p.current.ctrl.polymorphic_base values := by
  have effect := p.ref_is_null_reader byte size
  rw [accepted, WP.spec_ok] at effect
  exact ⟨effect.1, effect.2.1, effect.2.2 rfl⟩

end Itasca.Compiler

end

/-! ## Stateful Reader References -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

private theorem fixed_effect_concrete {before after inputs output}
    (known : ConcreteStack before) (effect : Simd.FixedEffect false before inputs output after) :
    ConcreteStack after := by
  obtain ⟨front,afterTypes,beforeRealized⟩ := effect _ (Body.Stack.realizes_default false after)
  have beforeConcrete := concrete_realization known beforeRealized
  apply stack_types_concrete
  rw [afterTypes]
  intro member
  rcases List.mem_append.mp member with member | member
  · exact beforeConcrete (List.mem_append_left _ member)
  · cases output with
    | none => simp [Simd.outputTypes] at member
    | some ty => cases ty <;> simp [Simd.outputTypes,Translation.valueType] at member

/-- Reference tests derive their concrete live suffix from the canonical fixed
effect; dead polymorphic paths only retain the exact source zipper. -/
theorem reader_ref_is_null_post {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    StatefulReaderPost p out .refIsNull := by
  obtain ⟨controls,position,rt,values,effect,post⟩ := reader_ref_is_null p out byte size accepted
  refine ⟨values,post,?_⟩
  intro C matched known monomorphic
  obtain ⟨sourceC,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  obtain ⟨outerKnown,currentKnown⟩ := concrete_stack_append.mp (stack ▸ known)
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  have afterKnown := fixed_effect_concrete currentKnown effect
  obtain ⟨C',outer',spine',header',base',typed',ctrls',blocks',stack'⟩ := post.opened
  have outerEq : outer' = outer := (spine_values spine').trans (spine_values spine).symm
  refine ⟨Body.Stack.stackTypes outer ++ front,Simd.inputTypes [Module.Constants.referenceValueType rt],
    Simd.outputTypes (some .I32),?_,?_,?_,?_⟩
  · simpa [Simd.inputTypes,Simd.outputTypes,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.map_cons,List.map_nil,reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using
      SourceMachine.Stateful.Signature.refIsNull (C := C) (Translation.referenceType rt)
  · simp only [stack,Body.Stack.stackTypes,List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance,Body.Stack.stackTypes,List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes values = _
    rw [afterTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance]
    exact concrete_stack_append.mpr ⟨outerKnown,afterKnown⟩

theorem reader_ref_func_post {data env locals index st}
    (p : Pending data env locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    StatefulReaderPost p out (.refFunc idx.val) := by
  obtain ⟨bound,controls,values,post⟩ := reader_ref_func p idx out byte size accepted
  refine ⟨_,post,?_⟩
  intro C matched known _
  refine ⟨Body.Stack.stackTypes st.core.vals.val,[],[valtype.FUNCREF],?_,by simp,?_,?_⟩
  · apply SourceMachine.Stateful.Signature.refFunc idx.val (Translation.Environment.funcType env.func_types.val[idx.val])
    simp [matched.funcs,List.getElem?_eq_getElem bound]
  · simp [values,Body.Stack.stackTypes,Translation.valueType]
  · rw [values]
    exact concrete_stack_append.mpr ⟨known,by simp [ConcreteStack]⟩

end Itasca.Compiler

end

end

/-! ## TypedSelectEmission -/

section

/-!
Accepted explicit-select bytes and their actual callback produce the typed emission and exact complete stack transition used by body compilation.

Main declarations: `reader_emit_typed_select`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Accepted explicit-select bytes and their actual callback produce the typed
emission and exact complete stack transition used by body compilation. -/
theorem reader_emit_typed_select {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (ty : wasm_types.ValueType) (front : List valtype) (values : List code.StackType) (emitted : runtime.bytecode.Instr),
      Body.Stack.stackTypes st.core.vals.val = front ++ [Translation.valueType ty,Translation.valueType ty,.I32] ∧
      Body.ReaderPost p out.core (.SELECT (some [Translation.valueType ty])) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ [Translation.valueType ty]) ∧
      TypedSelectEmission C (front ++ [Translation.valueType ty,Translation.valueType ty,.I32])
        (.SELECT (some [Translation.valueType ty])) [emitted] (front ++ [Translation.valueType ty]) := by
  obtain ⟨capacity,_⟩ := scalar_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index 28#u8 before after (by decide) accepted
  obtain ⟨ty,position,callback,read,controls,cursor,values,effect,post⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨front,types,beforeTypes,concrete,output⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  simp only [Body.Simd.inputTypes,Body.Simd.outputTypes,List.reverse_cons,List.reverse_nil,
    List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,Translation.valueType] at beforeTypes output
  rw [beforeTypes] at layout
  have lowered := compiler_typed_select_emission ops law before out.core types C front (Translation.valueType ty)
    localsMatch layout reachable concrete output codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select true) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select true) callback
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨ordinary,sources,cursor,ty,front,values,emitted,beforeTypes,post,
    ⟨lower,SourceStack.of_map types concrete output⟩,emission⟩

end Itasca.Compiler

end

end

/-! ## StructuredCompilerTypedSelect -/

section

/-!
Typed-select compilation through a structured reader state.

Main declarations: `StructuredReaderCompilerState.typed_select`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.typed_select {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit}
    (embedding : ∀ {input instruction code output}, TypedSelectEmission C input instruction code output → emit input instruction code output)
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPoint jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨entered,retained⟩ := state.compiled.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := state.compiled.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := state.compiled.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,ty,front,values,emitted,input,post,lowered,emission⟩ :=
      reader_emit_typed_select p ops law before after out ctx C
        (contextLocals.trans retained.localsEq.symm).symm (state.compiled.known live) (state.reach.current live)
        retained.layout live codeFits sourceFits coordinateFits byte accepted
    have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
    have compiled := state.compiled.ordinary live ordinary lowered (input ▸ embedding emission) sources consumed (by rw [cursor])
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨ty,position,callback,read,controls,cursor,values,effect,post⟩ := reader_typed_select p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
    obtain ⟨compiled,dead⟩ := post.structured_skip ops law state.compiled live
      (compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback)
      (compiler_core_sources ops law before after out.core (.select true) callback)
      (compiler_core_cursor ops law before after out.core (.select true) callback)
      28#u16 0#u32 0#u32 0#u128 callback
    exact (state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point
end Itasca.Compiler

end
