import Exec.Code.Local.Lowering.Common.LiteralSources
import Exec.Code.Local.Lowering.Integer.IntegerSources
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Lowering.Integer.IntegerCursor
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Integer.CompilerIntegerMetadata
import Exec.Code.Body.Reader.Calls.ReaderCallEffects
import Exec.Code.Body.Reader.Local.ReaderWasm1Local
import Exec.Code.Local.Lowering.Calls.LoweringCall
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

def FunctionParameterSlots {A : Type} (compiler : runtime.compiler.FunctionCompiler A) (env : module.Env) : Prop :=
  compiler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType))

theorem FunctionParameterSlots.lookup {A : Type} {compiler : runtime.compiler.FunctionCompiler A} {env}
    (metadata : FunctionParameterSlots compiler env) (index : U32) (ft : types.FuncType)
    (found : env.func_types.val[index.val]? = some ft) :
    ∃ word : U32, compiler.func_param_slots.val[index.val]? = some word ∧
      word.val = slots (ft.params.val.map Translate.valueType) := by
  have atIndex := congrArg (fun values => values[index.val]?) metadata
  simp only [List.getElem?_map, found, Option.map_some] at atIndex
  exact Option.map_eq_some_iff.mp atIndex

/-- The accepted reader determines both the direct-call signature and its
literal emitted CALL. Parameter slot metadata is the actual scheduler table. -/
theorem reader_emit_call_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 16#u8 before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ft : types.FuncType) (values : List code.StackType) (front : List valtype) (base : U32),
      env.func_types.val[index.val]? = some ft ∧
      Sequence.stackTypes st.core.vals.val = front ++ ft.params.val.map Translate.valueType ∧
      ReaderPostWasm2 p out.core (.CALL (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      base.val = slots (compilerLocals before) + slots front ∧
      TypedLowered before after out.core.vals.val (.Call index base) (front ++ ft.results.val.map Translate.valueType)) := by
  obtain ⟨index, values, callback, read, post⟩ := reader_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  obtain ⟨ft, rest, found, afterValues, transfer⟩ := reader_call_info_effect st out data env index outer p.current.vals vals
    (by simpa [Control.base, controls] using base) read
  have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic, controls] using monomorphic
  rw [poly] at transfer
  obtain ⟨front, beforeTypes, concrete⟩ := call_full_stack_types ft.params.val ft.results.val known vals afterValues transfer
  obtain ⟨parameterSlots, parameterLookup, parameterWidth⟩ := metadata.lookup index ft found
  rw [beforeTypes] at layout
  have slotBound : slots (compilerLocals before) + slots (front.map Translate.valueType) < 2^32 := by
    have bound := before.height.hBounds
    rw [layout.height, slots_append] at bound
    scalar_tac
  let callBase : U32 := UScalar.ofNatCore (slots (compilerLocals before) + slots (front.map Translate.valueType)) slotBound
  have position : callBase.val = slots (compilerLocals before) + slots (front.map Translate.valueType) := rfl
  have arguments : before.height.val = callBase.val + parameterSlots.val := by
    rw [layout.height, slots_append, position, parameterWidth, Nat.add_assoc]
  have lowered := lower_call ops law before out.core (front ++ ft.results.val)
    (front.map Translate.valueType ++ ft.params.val.map Translate.valueType) index parameterSlots callBase
    layout reachable parameterLookup arguments concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op16_ordinary_result ops law before after out.core index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op16_sources ops law before after out.core index 0#u32 0#u128 callback
  have cursor := compiler_op16_cursor ops law before after out.core index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  refine ⟨index, ft, values, front.map Translate.valueType, callBase, found, beforeTypes, post, position, ?_⟩
  refine ⟨?_, SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
  simpa only [List.map_append] using lowered rfl

/-- The accepted reader determines both the direct-call signature and its
literal emitted CALL. Parameter slot metadata is the actual scheduler table. -/
theorem reader_emit_call_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.pos ∧
    (∃ (index : U32) (ft : types.FuncType) (values : List code.StackType) (front : List valtype) (base : U32),
      env.func_types.val[index.val]? = some ft ∧
      Sequence.stackTypes st.vals.val = front ++ ft.params.val.map Translate.valueType ∧
      ReaderPostWasm1 p out (.CALL (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      base.val = slots (compilerLocals before) + slots front ∧
      TypedLowered before after out.vals.val (.Call index base) (front ++ ft.results.val.map Translate.valueType)) := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨index, values, callback, read, post⟩ := reader_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  obtain ⟨ft, rest, found, afterValues, transfer⟩ := reader_call_effect_wasm1 st out data env index outer p.current.vals vals
    (by simpa [Control.base, controls] using base) capacity read
  have poly : Control.polymorphic st = false := by simpa [Control.polymorphic, controls] using monomorphic
  rw [poly] at transfer
  obtain ⟨front, beforeTypes, concrete⟩ := call_full_stack_types ft.params.val ft.results.val known vals afterValues transfer
  obtain ⟨parameterSlots, parameterLookup, parameterWidth⟩ := metadata.lookup index ft found
  rw [beforeTypes] at layout
  have slotBound : slots (compilerLocals before) + slots (front.map Translate.valueType) < 2^32 := by
    have bound := before.height.hBounds
    rw [layout.height, slots_append] at bound
    scalar_tac
  let callBase : U32 := UScalar.ofNatCore (slots (compilerLocals before) + slots (front.map Translate.valueType)) slotBound
  have position : callBase.val = slots (compilerLocals before) + slots (front.map Translate.valueType) := rfl
  have arguments : before.height.val = callBase.val + parameterSlots.val := by
    rw [layout.height, slots_append, position, parameterWidth, Nat.add_assoc]
  have lowered := lower_call ops law before out (front ++ ft.results.val)
    (front.map Translate.valueType ++ ft.params.val.map Translate.valueType) index parameterSlots callBase
    layout reachable parameterLookup arguments concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out 16#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op16_ordinary_result ops law before after out index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op16_sources ops law before after out index 0#u32 0#u128 callback
  have cursor := compiler_op16_cursor ops law before after out index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  refine ⟨index, ft, values, front.map Translate.valueType, callBase, found, beforeTypes, post, position, ?_⟩
  refine ⟨?_, SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
  simpa only [List.map_append] using lowered rfl

end Exec.Code
