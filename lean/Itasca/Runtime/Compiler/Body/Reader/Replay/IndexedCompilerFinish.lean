import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedReturnAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Safety.ProfileOrdinarySafety
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnSafety
import Itasca.Visitor.ReachedTableLabels
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompiledBody
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext

/-!
Sections, each formerly its own module: ReachedSafety, IndexedCompilerInitial, IndexedPointNonempty, IndexedCompilerFinish.
-/

/-! ## ReachedSafety -/

section

/-!
Normal return of a reader step at a reached compiler point.

Main declarations: `IndexedTableReaderCompilerPointWasm2.reader_total`. A direct consumer is `Compiler.Body.Relations.Replay.ReachedBodySafetyWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns locals
      data env sourceLocals index ft st)
    (namespaces : OrdinaryNamespaces initial env ⟨sourceLocals,ft.results⟩)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (opcode : U8) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      ⟨{st.core with pos:=next}⟩ data env ⟨sourceLocals,ft.results⟩ index opcode compiler
      ⦃out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have pending := state.boundary.pending next advance inbounds
  have ready := point.ordinary_ready namespaces ledger.observed bodyBound ledger.indirect ledger.simd ledger.constants
  by_cases table : opcode = 14#u8
  · subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br_table]
    apply compiler_table_reader_wasm2_total ops law compiler _ data env pending.opened.shape.core
      state.boundary.source_bound state.frames_length point.tables.depths _ state.compiled.sources ledger.fixups
      point.tables.targets ready.coordinateFits
    have budget := state.compiled.codeBudget
    unfold SourceCodeBudget at budget
    dsimp only
    omega
  by_cases control : opcode.val ∈ [2,3,4,5,11,12,13,15]
  · apply state.control_total ops law next advance inbounds _ opcode control _ ledger.observed ledger.fixups bodyBound
    obtain ⟨sigEq,_⟩ := state.compiled.metadata.fields
    simpa only [sigEq] using signatures
  · apply compiler_reader_profile_wasm2_ordinary_total ops law compiler ⟨{st.core with pos:=next}⟩ data env _ index opcode ready pending.opened.shape.core
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at control ⊢
    have tableNe : opcode.val ≠ 14 := fun h => table (UScalar.eq_of_val_eq h)
    tauto

end Itasca.Runtime.Compiler

end

/-! ## IndexedCompilerInitial -/

section

/-!
Initial structured compiler state for body replay.

Main declarations: `StructuredReaderCompilerStateWasm2.initial`. A direct consumer is `Compiler.Body.Relations.Table.PreparedTableInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.initial {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType) (index : U32) (ft : Itasca.wasm_types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (compiled : StructuredCompilerPrefix jumpTables emit compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      [] (SourceScope.initial (ft.results.val.map Translate.valueType)) [] 0) :
    StructuredReaderCompilerStateWasm2 jumpTables emit compiler compiler types functions (ft.results.val.map Translate.valueType) locals
      data env sourceLocals index ft (Wasm2.initial index) []
      (SourceScope.initial (ft.results.val.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨compiled, .initial data env sourceLocals index ft signature size,
    .initial (.TypeIndex index) 0#usize ft.params.val ft.results.val, ?_, .initial _, .initial _⟩
  exact ReaderReachability.initial _ _ _ _ rfl

end Itasca.Runtime.Compiler

end

/-! ## IndexedPointNonempty -/

section

/-!
The complete-profile reached reader likewise has an active source control frame.

Main declarations: `IndexedTableReaderCompilerPointWasm2.ctrls_nonempty`. A direct consumer is `Compiler.Body.Reader.Publication.SourcePublicationAdvanceWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete-profile reached reader likewise has an active source control frame. -/
theorem IndexedTableReaderCompilerPointWasm2.ctrls_nonempty {A : Type}
    {emit initial compiler types functions returns locals data env sourceLocals index ft st}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial compiler types functions returns locals data env sourceLocals index ft st) :
    st.core.ctrls.val ≠ [] := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := state.boundary.opened
  rw [controls]
  simp

end Itasca.Runtime.Compiler

end

/-! ## IndexedCompilerFinish -/

section

/-!
The final executable check turns a completed actual body compilation into its retained source certificate, with the original function-start metadata.

Main declarations: `StructuredCompiledBody.finish`. A direct consumer is `Compiler.Body.Relations.Entry.ExecutableEntryCompilerFinish`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The final executable check turns a completed actual body compilation into
its retained source certificate, with the original function-start metadata. -/
theorem StructuredCompiledBody.finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A}
    {emit types functions params declared results source}
    (body : StructuredCompiledBody final.function.jump_tables.val emit initial final types functions results (params ++ declared) source)
    (signature : types[initial.function.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (locals : initial.function.locals.val.map Translate.valueType = params ++ declared)
    (parameterSlots : initial.function.param_slots.val = slots params)
    (localSlots : initial.function.local_slots.val = slots (params ++ declared))
    (capacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (validated : core.result.Result Unit error.Error)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final validated = .ok (.Ok compiled, budget)) :
    ∃ epilogue, StructuredFunctionCode emit types functions params declared results source compiled epilogue := by
  obtain ⟨epilogue, stable, empty, code, ⟨src, count, srcWords, fetched⟩, ending, bound⟩ := body
  have sourceEq : src = initial.function.local_slots := by
    apply UScalar.eq_of_val_eq
    exact srcWords.trans localSlots.symm
  refine ⟨epilogue, indexed_compiler_finish_certificate ops initial final validated compiled budget emit types functions
    params declared results source epilogue stable signature locals parameterSlots localSlots capacity
    bound code ?_ ending accepted⟩
  exact ⟨count, by simpa only [sourceEq] using fetched⟩
end Itasca.Runtime.Compiler

end
