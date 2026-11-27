import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulMetadataPosts
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectAndStatefulCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Body.Bulk.Step
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Local.Lowering.Simd.ConstructionChecks
import Itasca.Runtime.Compiler.Local.Relations.LoweringEffects

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Stateful.

This module collects StatefulBase, ExtendedCapacity.
Each section documents its contracts and consumers.
-/

/-! ## StatefulBase -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Stateful.

This module collects StatefulBulkDispatch, StatefulBase.
Each section documents its contracts and consumers.
-/

/-! ## StatefulBulkDispatch -/

section

/-!
Composition of bulk stateful reader cases.

Main declarations: `reader_stateful_bulk`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body
set_option maxRecDepth 2048

theorem reader_stateful_bulk {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_body visitor st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ op a b, StatefulArguments op a b ∧
      statefulCallback visitor before out.core op a b = .ok (.Ok (),after) ∧ StatefulReaderPost p out.core op := by
  obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 252#u8 before after (by decide) accepted
  have extended : 8 ≤ subopcode.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  rw [code.step_wasm2.bulk _ _ _ _ _ subopcode next _ decoded extended,code.step_bulk.eq_runs] at run
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member | member | member | member
  · have equal : subopcode = 8#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.memoryInit value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_memory_init_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 9#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.dataDrop value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_data_drop_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 10#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨.memoryCopy,0#u32,0#u32,⟨rfl,rfl⟩,?_,reader_memory_copy_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 11#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨.memoryFill,0#u32,0#u32,⟨rfl,rfl⟩,?_,reader_memory_fill_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 12#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableInit value.2.val value.1.val),value.1,value.2,⟨rfl,rfl⟩,?_,reader_table_init_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 13#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.elemDrop value.1.val),value.1,0#u32,⟨rfl,rfl⟩,?_,reader_elem_drop_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 14#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableCopy value.1.val value.2.val),value.1,value.2,⟨rfl,rfl⟩,?_,reader_table_copy_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 15#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableGrow value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_grow_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 16#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableSize value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_size_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 17#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableFill value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_fill_post p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback

end Itasca.Compiler

end

/-! ## StatefulBase -/

section

/-!
Composition of base stateful reader cases.

Main declarations: `reader_stateful_base`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body
set_option maxRecDepth 2048

theorem reader_stateful_base {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_body visitor st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    ∃ op a b, StatefulArguments op a b ∧
      statefulCallback visitor before out.core op a b = .ok (.Ok (),after) ∧ StatefulReaderPost p out.core op := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member
  · have equal : opcode = 37#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 37#u8 before after (by decide) accepted
    rw [code.step_wasm2.table_get] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableGet value.val),value,0#u32,?_,?_,reader_table_get_post p byte size value out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 38#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 38#u8 before after (by decide) accepted
    rw [code.step_wasm2.table_set] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.tableSet value.val),value,0#u32,?_,?_,reader_table_set_post p byte size value out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 63#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 63#u8 before after (by decide) accepted
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at run
    have dispatch := code.step_memory_size.dispatch visitor st.core data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    cases value
    refine ⟨.memorySize,0#u32,0#u32,?_,?_,reader_memory_size_post p byte size out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 64#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 64#u8 before after (by decide) accepted
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at run
    have dispatch := code.step_memory_grow.dispatch visitor st.core data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    cases value
    refine ⟨.memoryGrow,0#u32,0#u32,?_,?_,reader_memory_grow_post p byte size out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 208#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 208#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_null] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.refNull (Translation.referenceType value)),(match value with | .FuncRef => 0#u32 | .ExternRef => 1#u32),0#u32,?_,?_,reader_ref_null_post p byte size value out.core read⟩
    · cases value <;> exact ⟨rfl,rfl⟩
    · cases value <;> simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 209#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 209#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_is_null] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    cases value
    refine ⟨.refIsNull,0#u32,0#u32,?_,?_,reader_ref_is_null_post p out.core byte size read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback
  · have equal : opcode = 210#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := scalar_success visitor st out data env ctx index 210#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_func] at run
    obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
    refine ⟨(.refFunc value.val),value,0#u32,?_,?_,reader_ref_func_post p value out.core byte size read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translation.referenceType] using callback

end Itasca.Compiler

end

end

/-! ## ExtendedCapacity -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Stateful.

This module collects ExtendedScratch, ExtendedCodeMonotone, ExtendedFullCapacity.
Each section documents its contracts and consumers.
-/

/-! ## ExtendedScratch -/

section

/-!
Scratch-depth preservation for indirect calls, typed select and SIMD reader events.

Main declarations: `reader_indirect_call_depths` and `SimdReaderEvent.depths`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_indirect_call_depths {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_depths ops law before after out.core idx table (.Ok ()) callback

theorem reader_typed_select_depths {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_depths ops law before after out.core (.select true) callback

theorem SimdReaderEvent.depths {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : after.table_depths = before.table_depths := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact compiler_lower_simd_depths ops law before after out event.opcode event.a event.b event.bits
    (by omega) (by omega) event.callback

end Itasca.Compiler

end

/-! ## ExtendedCodeMonotone -/

section

/-!
Emitted-code monotonicity for indirect calls, typed select and SIMD reader events.

Main declarations: `reader_indirect_call_code_mono` and `SimdReaderEvent.code_mono`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_indirect_call_code_mono {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_code_mono ops law before after out.core idx table (.Ok ()) callback

theorem reader_typed_select_code_mono {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_code_mono ops law before after out.core (.select true) callback

theorem SimdReaderEvent.code_mono {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : before.function.code.val.length ≤ after.function.code.val.length := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact compiler_lower_simd_code_mono ops law before after out event.opcode event.a event.b event.bits
    (by omega) (by omega) event.callback

end Itasca.Compiler

end

/-! ## ExtendedFullCapacity -/

section

/-! ## StatefulEmission -/

section

/-!
The actual compiler callback and exact reader post determine an emitted stateful instruction and the complete append to its function-local pair table.

Main declarations: `StatefulReaderPost.emission`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- The actual compiler callback and exact reader post determine an emitted
stateful instruction and the complete append to its function-local pair table. -/
theorem StatefulReaderPost.emission {data env locals index st}
    {p : Pending data env locals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (C : context) (a b : U32)
    (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (matched : Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
      (∃ extra,after.function.indirect.val = before.function.indirect.val ++ extra) ∧
      ∃ values emitted output, Body.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
        TypedLowered before after out.vals.val emitted output ∧
        StatefulEmission after.function.indirect.val C (Body.Stack.stackTypes st.core.vals.val)
          op.source [emitted] output := by
  obtain ⟨values,sourcePost,typesPost⟩ := post
  obtain ⟨front,input,output,signature,beforeTypes,afterTypes,afterKnown⟩ := typesPost C matched known monomorphic
  obtain ⟨types,concrete⟩ := (concrete_stack_iff _).mp afterKnown
  have typed : types.map Translation.valueType = front ++ output := by
    simpa only [concrete,Body.Stack.stackTypes,List.map_map,Function.comp_def] using afterTypes
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_stateful_emission ops law before after out types C front
    input output op a b signature contextLocals arguments layout reachable concrete typed codeFits sourceFits coordinateFits callback
  exact ⟨compiler_stateful_ordinary_result ops law before after out _ _ _ (.Ok ()) callback,
    compiler_stateful_sources ops law before after out _ _ _ callback,
    compiler_stateful_cursor ops law before after out _ _ _ callback,pairs,values,emitted,front ++ output,
    sourcePost,⟨lowered,afterKnown,afterTypes⟩,beforeTypes ▸ emission⟩

end Itasca.Compiler

end

/-! ## ExtendedFullCapacity -/

section

/-!
Capacity follows the actual scalar/reference callback and canonical reader state.

Main declarations: `reader_stateful_base_full_capacity` and `reader_typed_select_full_capacity`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Capacity follows the actual scalar/reference callback and canonical reader state. -/
theorem reader_stateful_base_full_capacity {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_capacity ops law before after out.core op a b callback

theorem reader_stateful_bulk_full_capacity {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_capacity ops law before after out.core op a b callback

theorem reader_indirect_call_full_capacity {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_call_capacity ops law before after out.core idx table callback

theorem reader_typed_select_full_capacity {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_core_capacity ops law before after out.core (.select true) callback

end Itasca.Compiler

end

end

end
