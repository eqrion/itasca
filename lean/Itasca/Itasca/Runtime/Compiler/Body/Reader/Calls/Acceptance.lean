import Itasca.Runtime.Compiler.Body.Relations.ExecutableEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Body.Trace.BytesDispatch
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout

open WebAssembly

open Itasca.Representation

/-! ## IndirectEmission -/

section

/-!
The canonical reader and actual compiler callback jointly establish the indirect-call emission, with metadata and source cursor preserved.

Main declarations: `reader_emit_indirect_call`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- The canonical reader and actual compiler callback jointly establish the
indirect-call emission, with metadata and source cursor preserved. -/
theorem reader_emit_indirect_call {data env locals typeIndex st}
    (p : Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (matched : Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ index table values emitted output,
      after.function.indirect.val = before.function.indirect.val ++ [(table,index)] ∧
      Body.ReaderPost p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted output ∧
      IndirectCallEmission after.function.indirect.val C (Body.Stack.stackTypes st.core.vals.val)
        (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) [emitted] output := by
  obtain ⟨index,table,values,callback,read,post⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨_,outer,_,_,base,_,controls,_,vals⟩ := p.opened
  have poly : Body.Control.polymorphic st.core = false := by
    simpa [Body.Control.polymorphic,controls] using monomorphic
  obtain ⟨ft,tt,front,typeFound,tableFound,elem,beforeTypes,concrete⟩ := reader_indirect_call_stack st out data env index table
    outer p.current.vals vals (by simpa [Body.Control.base,controls] using base) known poly p.opened.shape.core read
  have sourceType : C.TYPES[index.val]? = some ⟨.mk_list (ft.params.val.map Translation.valueType),.mk_list (ft.results.val.map Translation.valueType)⟩ := by
    simp [matched.types,List.getElem?_map,typeFound,Translation.Environment.funcType]
  have sourceTable : C.TABLES[table.val]? = some (.mk_tabletype (Translation.Environment.limitsType tt.limits) .FUNCREF) := by
    simp [matched.tables,List.getElem?_map,tableFound,Translation.Environment.tableType,elem,Translation.referenceType]
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_indirect_call_emission_captured ops law before after out.core
    (front ++ ft.results.val) env.types.val signatures C matched.types (front.map Translation.valueType)
    (ft.params.val.map Translation.valueType) (ft.results.val.map Translation.valueType) index table
    (Translation.Environment.limitsType tt.limits) sourceType sourceTable contextLocals layout reachable concrete
    (by simp) codeFits sourceFits coordinateFits callback
  refine ⟨compiler_indirect_call_ordinary_result ops law before after out.core index table (.Ok ()) callback,
    compiler_indirect_call_sources ops law before after out.core index table callback,
    compiler_indirect_call_cursor ops law before after out.core index table callback,
    index,table,values,emitted,_,pairs,post,?_,beforeTypes ▸ emission⟩
  exact ⟨lowered,SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
end Itasca.Compiler

end

/-! ## IndirectCallPrefix -/

section

/-!
A fixed future pair table suffices for both sides of indirect-call lowering. Dead paths retain the exact reader advance without requiring concrete operands.

Main declarations: `structured_reader_prefix_indirect_call`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A fixed future pair table suffices for both sides of indirect-call lowering.
Dead paths retain the exact reader advance without requiring concrete operands. -/
theorem structured_reader_prefix_indirect_call {jumpTables : List U32} {data env sourceLocals typeIndex st}
    (p : Body.Pending data env sourceLocals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (future : List (U32 × U32))
    {emit types functions returns locals parents current}
    (embedding : ∀ input instruction emitted output,
      IndirectCallEmission (after.function.indirect.val ++ future) C input instruction emitted output →
        emit input instruction emitted output)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 before = .ok (.Ok (),out,after)) :
    ∃ (index table : U32) (values : List code.StackType) (extra : List (U32 × U32)),
      after.function.indirect.val = before.function.indirect.val ++ extra ∧
      Body.ReaderPost p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (current.advance (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val))) out.core.vals.val out.core.pos.val ∧
      after.reachable = before.reachable := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,index,table,values,emitted,output,pairs,reader,lowered,emission⟩ :=
      reader_emit_indirect_call p ops law before after out ctx C matched
        (contextLocals.trans retained.localsEq.symm) signatures (invariant.known reachable)
        (monomorphic reachable) retained.layout reachable codeFits sourceFits coordinateFits byte accepted
    have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := reader.span; omega
    exact ⟨index,table,values,[(table,index)],pairs,reader,
      invariant.ordinary reachable ordinary lowered (embedding _ _ _ _ (emission.append_pairs future))
        sources consumed (by rw [cursor]),lowered.1.2.2.2.1⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨index,table,values,callback,read,reader⟩ := reader_indirect_call p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
    have frame := compiler_dead_op_frame ops law before out.core 17#u16 index table 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    have pairs : after.function.indirect.val = before.function.indirect.val ++ [] := by
      dsimp only at frame
      rw [frame]; simp
    obtain ⟨compiled,deadAfter⟩ := reader.structured_skip ops law invariant dead
      (compiler_indirect_call_ordinary_result ops law before after out.core index table (.Ok ()) callback)
      (compiler_indirect_call_sources ops law before after out.core index table callback)
      (compiler_indirect_call_cursor ops law before after out.core index table callback)
      17#u16 index table 0#u128 callback
    exact ⟨index,table,values,[],pairs,reader,compiled,deadAfter.trans dead.symm⟩
end Itasca.Compiler

end

/-! ## IndirectPairPrefix -/

section

/-!
The compiler index-pair prefix of an indirect-call reader step.

Main declarations: `reader_indirect_call_pair_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem reader_indirect_call_pair_prefix {jumpTables : List U32} {data env sourceLocals typeIndex st}
    (p : Body.Pending data env sourceLocals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 before = .ok (.Ok (),out,after)) :
    ∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,index,table,values,emitted,output,pairs,reader,lowered,emission⟩ :=
      reader_emit_indirect_call p ops law before after out ctx C matched
        (contextLocals.trans retained.localsEq.symm) signatures (invariant.known reachable)
        (monomorphic reachable) retained.layout reachable codeFits sourceFits coordinateFits byte accepted
    exact ⟨[(table,index)],pairs⟩
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    obtain ⟨index,table,values,callback,read,reader⟩ := reader_indirect_call p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
    have frame := compiler_dead_op_frame ops law before out.core 17#u16 index table 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    have pairs : after.function.indirect.val = before.function.indirect.val ++ [] := by
      dsimp only at frame
      rw [frame]; simp
    exact ⟨[],pairs⟩

end Itasca.Compiler

end

/-! ## CallLowering -/

section

/-!
Direct-call lowering under the function parameter-slot certificate.

Main declarations: `FunctionParameterSlots` and `reader_emit_call`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

def FunctionParameterSlots {A : Type} (compiler : runtime.compiler.FunctionCompiler A) (env : metadata.Env) : Prop :=
  compiler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType))

theorem FunctionParameterSlots.lookup {A : Type} {compiler : runtime.compiler.FunctionCompiler A} {env}
    (metadata : FunctionParameterSlots compiler env) (index : U32) (ft : wasm_types.FuncType)
    (found : env.func_types.val[index.val]? = some ft) :
    ∃ word : U32, compiler.func_param_slots.val[index.val]? = some word ∧
      word.val = slots (ft.params.val.map Translation.valueType) := by
  have atIndex := congrArg (fun values => values[index.val]?) metadata
  simp only [List.getElem?_map, found, Option.map_some] at atIndex
  exact Option.map_eq_some_iff.mp atIndex

/-- The accepted reader determines both the direct-call signature and its
literal emitted CALL. Parameter slot metadata is the actual scheduler table. -/
theorem reader_emit_call {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 16#u8 before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (index : U32) (ft : wasm_types.FuncType) (values : List code.StackType) (front : List valtype) (base : U32),
      env.func_types.val[index.val]? = some ft ∧
      Body.Stack.stackTypes st.core.vals.val = front ++ ft.params.val.map Translation.valueType ∧
      Body.ReaderPost p out.core (.CALL (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      base.val = slots (compilerLocals before) + slots front ∧
      TypedLowered before after out.core.vals.val (.Call index base) (front ++ ft.results.val.map Translation.valueType)) := by
  obtain ⟨index, values, callback, read, post⟩ := reader_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  obtain ⟨ft, rest, found, afterValues, transfer⟩ := reader_call_info_effect st out data env index outer p.current.vals vals
    (by simpa [Body.Control.base, controls] using base) read
  have poly : Body.Control.polymorphic st.core = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
  rw [poly] at transfer
  obtain ⟨front, beforeTypes, concrete⟩ := call_full_stack_types ft.params.val ft.results.val known vals afterValues transfer
  obtain ⟨parameterSlots, parameterLookup, parameterWidth⟩ := metadata.lookup index ft found
  rw [beforeTypes] at layout
  have slotBound : slots (compilerLocals before) + slots (front.map Translation.valueType) < 2^32 := by
    have bound := before.height.hBounds
    rw [layout.height, slots_append] at bound
    scalar_tac
  let callBase : U32 := UScalar.ofNatCore (slots (compilerLocals before) + slots (front.map Translation.valueType)) slotBound
  have position : callBase.val = slots (compilerLocals before) + slots (front.map Translation.valueType) := rfl
  have arguments : before.height.val = callBase.val + parameterSlots.val := by
    rw [layout.height, slots_append, position, parameterWidth, Nat.add_assoc]
  have lowered := lower_call ops law before out.core (front ++ ft.results.val)
    (front.map Translation.valueType ++ ft.params.val.map Translation.valueType) index parameterSlots callBase
    layout reachable parameterLookup arguments concrete codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 index 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op16_ordinary_result ops law before after out.core index 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op16_sources ops law before after out.core index 0#u32 0#u128 callback
  have cursor := compiler_op16_cursor ops law before after out.core index 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  refine ⟨index, ft, values, front.map Translation.valueType, callBase, found, beforeTypes, post, position, ?_⟩
  refine ⟨?_, SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
  simpa only [List.map_append] using lowered rfl

end Itasca.Compiler

end

/-! ## Acceptance -/

section

/-!
Successful direct and indirect call replay from reached source prefixes and allocator availability. These acceptance directions complement inverse accepted-step facts.
-/

/-! ## Reached Call Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Independently accepted Wasm 2 calls determine their source parameter
signature and live layout. Captured scheduler metadata then justifies actual
compiler call acceptance and its single instruction charge. -/
theorem reached_call_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (demand : CallbackDemand compiler out.core bound) (metadata : FunctionParameterSlots compiler env)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (reference : code.step_body source st data env ctx index 16#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 16#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨callee,_,_,read,_⟩ := reader_call p source before after out ctx byte reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call compiler out.core callee ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 16#u16 callee 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
      obtain ⟨ft,rest,found,afterValues,transfer⟩ := reader_call_info_effect st out data env callee outer p.current.vals values
        (by simpa [Body.Control.base,controls] using base) read
      have poly : Body.Control.polymorphic st.core = false := by simpa [Body.Control.polymorphic,controls] using monomorphic live
      rw [poly] at transfer
      obtain ⟨front,beforeTypes,_⟩ := call_full_stack_types ft.params.val ft.results.val (known live) values afterValues transfer
      obtain ⟨parameterSlots,lookup,width⟩ := metadata.lookup callee ft found
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      exact compiler_call_available ops bound available compiler out.core demand (front.map Translation.valueType)
        (ft.params.val.map Translation.valueType) callee parameterSlots (fun _ => layout) (fun _ => lookup) width
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out.core 16#u16 callee 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  rw [Body.CallbackTrace.dispatch_call]
  exact Body.CallbackTrace.bodyRun.available_of_read _
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) .call compiler callee out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Compiler

end

/-! ## Reached Indirect Call Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Independent Wasm 2 indirect-call validation determines both source
indices and the full live parameter/selector layout. Captured signatures and
bounded pair storage then establish actual compiler acceptance. -/
theorem reached_indirect_call_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (demand : CallbackDemand compiler out.core bound)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (reference : code.step_body source st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨callee,table,_,_,read,_⟩ := reader_indirect_call p source before after out ctx byte reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call_indirect
      compiler out.core callee table ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 17#u16 callee table 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
      have poly : Body.Control.polymorphic st.core = false := by simpa [Body.Control.polymorphic,controls] using monomorphic live
      obtain ⟨ft,_,front,typeFound,_,_,beforeTypes,_⟩ := reader_indirect_call_stack st out data env callee table
        outer p.current.vals values (by simpa [Body.Control.base,controls] using base) (known live) poly p.opened.shape.core read
      obtain ⟨signature,selected,matched⟩ := signatures.select (bt := .TypeIndex callee) (ins := ft.params.val) (outs := ft.results.val)
        (by simp [Body.inputs,Body.resolve,typeFound]) (by simp [Body.outputs,Body.resolve,typeFound])
      have found : compiler.signatures.val[callee.val]? = some signature := by
        cases selected with
        | index _ _ found => exact found
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      have pc := demand.pc
      have capacity := demand.codeCapacity
      have reserve := demand.codeReserve
      simp only [alloc.vec.Vec.length] at pairs pc capacity reserve
      exact compiler_indirect_call_available ops bound available compiler out.core demand (front.map Translation.valueType)
        (ft.params.val.map Translation.valueType) callee table signature (fun _ => layout) (fun _ => found)
        matched.paramWords
        (by change compiler.function.indirect.val.length ≤ U32.max; omega)
        (by change compiler.function.indirect.val.length < Usize.max; omega)
        (by change compiler.function.indirect.val.length+1 ≤ bound; omega)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out.core 17#u16 callee table
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  rw [Body.CallbackTrace.dispatch_call_indirect]
  exact Body.CallbackTrace.bodyRun.available_of_read _
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun arg : U32 × U32 => .call_indirect arg.1 arg.2)
    compiler (callee,table) out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Compiler

end

end
