import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Local.Relations.Function.EntryTypedSteps
import Itasca.Module.Code.ReachedEntry
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget

/-!
Sections, each formerly its own module: FunctionStartFacts, EntryCompilerInitial, PreparedCompilerStart, PreparedRawInitial.
-/

/-! ## FunctionStartFacts -/

section

/-!
Fixed metadata and local layout obtained from actual construction and the successful function-start callback. These are static premises of the body fold.

Main declarations: `compiler_function_start_facts` and `function_body_coordinate_bound`. A direct consumer is `Compiler.Body.Relations.Entry.EntryCompilerInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Fixed metadata and local layout obtained from actual construction and the
successful function-start callback. These are static premises of the body fold. -/
theorem compiler_function_start_facts {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    LocalLayout started ∧ started.function.locals = ctx.locals ∧
      started.function.slot_count = started.function.local_slots ∧
      started.function.param_slots = signature.param_slots ∧
      started.function.type_index = typeIndex ∧
      started.function.body_start.val = batchStart.val + bodyBegin.val ∧
      started.function.body_end.val = batchStart.val + bodyEnd.val ∧
      started.signatures = signatures ∧ started.func_param_slots = functionSlots ∧
      started.batch_start = batchStart := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at newPost
  obtain ⟨localLayout, emptyLocals, emptyOperands, emptyMaps, emptyFrames, _, _,
    sigs, functionWidths, coordinate⟩ := newPost
  have startPost := compiler_function_start ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals localLayout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [accepted, WP.spec_ok] at startPost
  obtain ⟨layout, _, capacity, localTypes, params, typeIdx, start, finish, _, _, _⟩ := startPost rfl
  have environment := compiler_function_start_environment_frame ops law initial started ctx typeIndex bodyBegin bodyEnd
    (.Ok ()) accepted
  have fields : started.signatures = initial.signatures ∧
      started.func_param_slots = initial.func_param_slots ∧ started.batch_start = initial.batch_start := by
    simpa only [FunctionEnvironment, Prod.mk.injEq] using environment
  refine ⟨⟨layout.localSlots, layout.localOffsets⟩, ?_, capacity, params, typeIdx,
    ?_, ?_, fields.1.trans sigs, fields.2.1.trans functionWidths, fields.2.2.trans coordinate⟩
  · exact alloc.vec.Vec.ext _ _ localTypes
  · simpa only [coordinate] using start
  · simpa only [coordinate] using finish

/-- The exact byte span from the accepted entry bounds every body-relative
source coordinate after rebasing it to the module origin. -/
theorem function_body_coordinate_bound {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {data body : Slice U8}
    {bodyBegin bodyEnd batchStart : Usize}
    (span : Wasm1.BytesAt data bodyBegin body.val bodyEnd)
    (start : compiler.function.body_start.val = batchStart.val + bodyBegin.val)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max) :
    compiler.function.body_start.val + body.length ≤ Usize.max := by
  have length := span.length
  change bodyEnd.val = bodyBegin.val + body.length at length
  omega
end Itasca.Runtime.Compiler

end

/-! ## EntryCompilerInitial -/

section

/-!
The fixed data needed by the body fold is derived from the accepted entry and scheduler tables, before any opcode is compiled.

Main declarations: `CompilerEntryFacts`. A direct consumer is `Compiler.Body.Relations.Entry.ExecutableEntryCompilerFinish`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Lookup in the canonical source table selects an actual captured compiler
signature, including exact parameter and result widths. -/
theorem SignatureSequence.lookup_source {signatures types}
    (sequence : SignatureSequence signatures types) {index : Nat} {ty : Itasca.wasm_types.FuncType}
    (found : types[index]? = some ty) :
    ∃ signature, signatures[index]? = some signature ∧ SignatureMatches signature
      (ty.params.val.map Translate.valueType) (ty.results.val.map Translate.valueType) := by
  induction sequence generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst ty
      exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

/-- The fixed data needed by the body fold is derived from the accepted entry
and scheduler tables, before any opcode is compiled. -/
structure CompilerEntryFacts {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (ft : wasm_types.FuncType)
    (body : Slice U8) : Prop where
  localLayout : LocalLayout compiler
  locals : compiler.function.locals = ctx.locals
  capacity : compiler.function.slot_count = compiler.function.local_slots
  parameterSlots : compiler.function.param_slots.val = slots (ft.params.val.map Translate.valueType)
  typeIndex : compiler.function.type_index = index
  signatures : SignatureSequence compiler.signatures.val env.types.val
  functionSlots : FunctionParameterSlots compiler env
  bodyBound : compiler.function.body_start.val + body.length ≤ Usize.max

theorem witness_compiler_start {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    CompilerPrefix w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      [] (SourceScope.initial (w.ft.results.val.map Translate.valueType)) [] 0 := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨signature, lookup, matched⟩ := signatureTable.lookup_source sourceLookup
  have beginFits : batchStart.val + w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have facts := compiler_function_start_facts ops law signatures functionSlots budget batchStart initial w.startedState
    w.ctx w.typeIdx signature w.bodyStart finish lookup beginFits endFits created w.function_start
  obtain ⟨layout, locals, capacity, params, typeIndex, bodyStart, _, sigs, funcs, _⟩ := facts
  constructor
  · refine ⟨layout, locals, capacity, ?_, typeIndex, ?_, ?_, ?_⟩
    · rw [params]
      exact matched.paramWords
    · simpa only [sigs] using signatureTable
    · simpa only [FunctionParameterSlots, funcs] using functionTable
    · exact function_body_coordinate_bound w.body_bytes bodyStart endFits
  · exact compiler_function_start_prefix ops law signatures functionSlots budget batchStart initial w.startedState
      w.ctx w.typeIdx signature w.bodyStart finish _ _ _ lookup matched.resultWords beginFits endFits created w.function_start

theorem TypedRunWasm2.body_size {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after} (run : TypedRunWasm2 visitor data env ctx index st before after) :
    data.length ≤ limits.MAX_FUNCTION_BYTES.val := by
  cases run with
  | done typed _ _ => exact typed.bounds.size
  | step typed _ _ _ _ _ => exact typed.bounds.size

end Itasca.Runtime.Compiler

end

/-! ## PreparedCompilerStart -/

section

/-!
Entry framing and captured signature lookup justify every unchecked operation in the fresh function-start callback, including rejected allocation.

Main declarations: `prepared_compiler_start_total`. A direct consumer is `Compiler.Body.Relations.Entry.PreparedRawInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Entry framing and captured signature lookup justify every unchecked
operation in the fresh function-start callback, including rejected allocation. -/
theorem prepared_compiler_start_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish ⦃ _ => True ⦄ := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨signature,lookup,_⟩ := signatureTable.lookup_source sourceLookup
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨layout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  apply WP.spec_mono (compiler_function_start ops law initial w.ctx w.typeIdx signature
    w.bodyStart w.finish (by simpa only [sigs] using lookup)
    (by rw [batch]; have length := w.body_bytes.length; omega)
    (by simpa only [batch] using endFits) locals layout operands
    (by simp only [controls,List.length_nil]; scalar_tac)
    (by simp only [frames,List.length_nil]; scalar_tac))
  intros
  trivial

end Itasca.Runtime.Compiler

end

/-! ## PreparedRawInitial -/

section

/-!
Fresh entry establishes the raw operand and auxiliary-buffer ledger before any body byte is read. This includes bottom-capable observations used later.

Main declarations: `prepared_compiler_raw_initial`. A direct consumer is `Compiler.Module.PreparedExecutableSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Fresh entry establishes the raw operand and auxiliary-buffer ledger before
any body byte is read. This includes bottom-capable observations used later. -/
theorem prepared_compiler_raw_initial {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    ObservedStack started [] ∧
    started.function.indirect.val.length ≤ started.function.code.val.length ∧
    started.function.simd.val.length ≤ started.function.code.val.length ∧
    started.function.v128_pool.val.length ≤ started.function.code.val.length ∧
    FixupBudget started.frames.val started.function.code.val.length := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨signature,lookup,_⟩ := signatureTable.lookup_source sourceLookup
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨localLayout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  have post := compiler_function_start_raw ops law initial w.ctx w.typeIdx signature w.bodyStart w.finish
    (by simpa only [sigs] using lookup)
    (by rw [batch]; have length := w.body_bytes.length; omega)
    (by simpa only [batch] using endFits) locals localLayout operands
    (by simp only [controls,List.length_nil]; scalar_tac)
    (by simp only [frames,List.length_nil]; scalar_tac)
  rw [startedCall,WP.spec_ok] at post
  obtain ⟨layout,codeEq,framesEq,tablesEq⟩ := post rfl
  have initialTables : CompilerTables.ofFunction initial.function = .empty := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  have tables := tablesEq.trans initialTables
  have tableCounts := congrArg (fun t : CompilerTables =>
    (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.empty,List.length_nil,Prod.mk.injEq] at tableCounts
  refine ⟨⟨?_,?_⟩,by omega,by omega,by omega,?_⟩
  · simpa only [stackOffsets,List.length_nil,List.range_zero,List.map_nil,observedOffsets]
      using layout.operandOffsets
  · simpa [layout.localSlots,stackWords,Compiler.slots] using layout.height
  · simp [FixupBudget,framesEq,frames,alloc.vec.Vec.new]
end Itasca.Runtime.Compiler

end
