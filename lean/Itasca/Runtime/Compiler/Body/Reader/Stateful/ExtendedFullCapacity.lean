import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch

/-!
Sections, each formerly its own module: StatefulEmission, ExtendedFullCapacity.
-/

/-! ## StatefulEmission -/

section

/-!
The actual compiler callback and exact reader post determine an emitted stateful instruction and the complete append to its function-local pair table.

Main declarations: `StatefulReaderPost.emission`. A direct consumer is `Compiler.Body.Reader.Calls.IndirectPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- The actual compiler callback and exact reader post determine an emitted
stateful instruction and the complete append to its function-local pair table. -/
theorem StatefulReaderPost.emission {data env locals index st}
    {p : Pending data env locals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (C : context) (a b : U32)
    (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
      (∃ extra,after.function.indirect.val = before.function.indirect.val ++ extra) ∧
      ∃ values emitted output, Wasm2.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
        TypedLowered before after out.vals.val emitted output ∧
        StatefulEmission after.function.indirect.val C (Sequence.stackTypes st.core.vals.val)
          op.source [emitted] output := by
  obtain ⟨values,sourcePost,typesPost⟩ := post
  obtain ⟨front,input,output,signature,beforeTypes,afterTypes,afterKnown⟩ := typesPost C matched known monomorphic
  obtain ⟨types,concrete⟩ := (concrete_stack_iff _).mp afterKnown
  have typed : types.map Translate.valueType = front ++ output := by
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using afterTypes
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_stateful_emission ops law before after out types C front
    input output op a b signature contextLocals arguments layout reachable concrete typed codeFits sourceFits coordinateFits callback
  exact ⟨compiler_stateful_ordinary_result ops law before after out _ _ _ (.Ok ()) callback,
    compiler_stateful_sources ops law before after out _ _ _ callback,
    compiler_stateful_cursor ops law before after out _ _ _ callback,pairs,values,emitted,front ++ output,
    sourcePost,⟨lowered,afterKnown,afterTypes⟩,beforeTypes ▸ emission⟩

end Itasca.Runtime.Compiler

end

/-! ## ExtendedFullCapacity -/

section

/-!
Capacity follows the actual scalar/reference callback and canonical reader state.

Main declarations: `reader_stateful_base_full_capacity_wasm2` and `reader_typed_select_full_capacity_wasm2`. A direct consumer is `Compiler.Body.Capacity.ExecutableFunctionCapacity`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Capacity follows the actual scalar/reference callback and canonical reader state. -/
theorem reader_stateful_base_full_capacity_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_capacity ops law before after out.core op a b callback

theorem reader_stateful_bulk_full_capacity_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_capacity ops law before after out.core op a b callback

theorem reader_indirect_call_full_capacity_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_capacity ops law before after out.core idx table callback

theorem reader_typed_select_full_capacity_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_capacity ops law before after out.core (.select true) callback

end Itasca.Runtime.Compiler

end
