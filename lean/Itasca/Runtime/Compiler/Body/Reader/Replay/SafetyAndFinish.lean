import Itasca.Runtime.Compiler.Body.Reader.Safety.InstructionSafety
import Itasca.Runtime.Compiler.Body.Reader.Local.Compilation
import Itasca.Body.Scalar.Env
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdCallbackPublication
import Itasca.Body.Step.Total
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Body.Reader.Control.TerminalCompilationAndSafety
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Control.ControlPointsAndInitialPrefixes
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Local.Control.FunctionAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects OrdinarySafety, SafetyAndFinish.
Each section documents its contracts and consumers.
-/

/-! ## OrdinarySafety -/

section

/-! ## ScalarSafety -/

section

/-!
Normal return of scalar reader dispatch.

Main declarations: `compiler_reader_scalar_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_scalar_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Body.controlOpcodes) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases high : 69 ≤ opcode.val
  · exact compiler_reader_numeric_dispatch_total ops law compiler st data env ctx ready shape capacity opcode high
  by_cases memory : 40 ≤ opcode.val ∧ opcode.val ≤ 62
  · exact compiler_reader_memory_dispatch_total ops law compiler st data env ctx ready shape capacity opcode memory.1 memory.2
  by_cases h_nop : opcode = code.OP_NOP
  · subst opcode
    exact compiler_reader_nop_total ops law compiler st data env ctx ready shape capacity
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · subst opcode
    exact compiler_reader_unreachable_total ops law compiler st data env ctx ready shape capacity
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · subst opcode
    exact compiler_reader_i32_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · subst opcode
    exact compiler_reader_i64_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · subst opcode
    exact compiler_reader_f32_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · subst opcode
    exact compiler_reader_f64_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_drop : opcode = code.OP_DROP
  · subst opcode
    exact compiler_reader_drop_total ops law compiler st data env ctx ready shape capacity
  by_cases h_select : opcode = code.OP_SELECT
  · subst opcode
    exact compiler_reader_select_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · subst opcode
    exact compiler_reader_local_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · subst opcode
    exact compiler_reader_local_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · subst opcode
    exact compiler_reader_local_tee_total ops law compiler st data env ctx ready shape capacity
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · subst opcode
    exact compiler_reader_global_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · subst opcode
    exact compiler_reader_global_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · subst opcode
    exact compiler_reader_memory_size_total ops law compiler st data env ctx ready shape capacity
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · subst opcode
    exact compiler_reader_memory_grow_total ops law compiler st data env ctx ready shape capacity
  have reserved : (6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨
      (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
      (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨
      (37 ≤ opcode.val ∧ opcode.val ≤ 39) := by
    simp only [Body.controlOpcodes, List.mem_cons, not_or] at ordinary
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved _ st data env ctx opcode compiler reserved]
  simp
end Itasca.Compiler

end

/-! ## OrdinarySafety -/

section

/-!
Normal return of extended and complete ordinary reader dispatch.

Main declarations: `compiler_reader_extended_total` and `compiler_reader_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem compiler_reader_extended_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Body.controlOpcodes) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases sign : 192 ≤ opcode.val ∧ opcode.val ≤ 196
  · exact compiler_reader_sign_dispatch_total ops law compiler st data env ctx ready shape capacity opcode sign.1 sign.2
  have noSign : Body.NumericExtensions.signMeaning opcode = none := by
    unfold Body.NumericExtensions.signMeaning
    split <;> simp_all
  by_cases prefixed : opcode = 252#u8
  · subst opcode
    exact compiler_reader_saturating_dispatch_total ops law compiler st data env ctx ready shape capacity
  rw [code.step_extended.base _ st data env ctx opcode compiler noSign (by simpa only [code.OP_MISC_PREFIX] using prefixed)]
  exact compiler_reader_scalar_total ops law compiler st data env ctx ready shape capacity opcode ordinary

theorem compiler_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Body.controlOpcodes) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases h253 : opcode = 253#u8
  · subst opcode
    rw [code.step_wasm2.simd]
    exact compiler_reader_simd_total ops law compiler st data env ctx ready shape capacity
  by_cases h28 : opcode = 28#u8
  · subst opcode
    exact compiler_reader_typed_select_total ops law compiler st data env ctx ready shape capacity
  by_cases h37 : opcode = 37#u8
  · subst opcode
    exact compiler_reader_table_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h38 : opcode = 38#u8
  · subst opcode
    exact compiler_reader_table_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h208 : opcode = 208#u8
  · subst opcode
    exact compiler_reader_ref_null_total ops law compiler st data env ctx ready shape capacity
  by_cases h209 : opcode = 209#u8
  · subst opcode
    exact compiler_reader_ref_is_null_total ops law compiler st data env ctx ready shape capacity
  by_cases h210 : opcode = 210#u8
  · subst opcode
    exact compiler_reader_ref_func_total ops law compiler st data env ctx ready shape capacity
  by_cases h252 : opcode = 252#u8
  · rw [h252, code.step_wasm2.prefixed]
    obtain ⟨result,read,_⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
    simp only [Body.miscellaneousStep,read,bind_ok]
    cases result with
    | Err error => simp
    | Ok pair =>
      obtain ⟨subopcode,next⟩ := pair
      dsimp only at *
      split
      · exact compiler_reader_saturating_dispatch_total ops law compiler st data env ctx ready shape capacity
      · exact compiler_reader_bulk_total ops law compiler {st with pos := next} data env ctx subopcode
          ready ⟨shape.ordered,shape.bounded⟩ capacity
  rw [code.step_wasm2.base _ st data env ctx opcode compiler (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28,neq h37,neq h38,neq h208,neq h209,neq h210,neq h252,neq h253⟩)]
  exact compiler_reader_extended_total ops law compiler st data env ctx ready shape capacity opcode ordinary
end Itasca.Compiler

end

/-! ## OrdinarySafety -/

section

/-!
Normal return of ordinary reader steps with body capacity checks.

Main declarations: `compiler_reader_ordinary_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_ordinary_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Body.Control.Shape st.core)
    (ordinary : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  by_cases call : opcode = 16#u8
  · subst opcode
    exact compiler_reader_call_total ops law compiler st data env ctx index ready shape
  by_cases indirect : opcode = 17#u8
  · subst opcode
    exact compiler_reader_call_indirect_total ops law compiler st data env ctx index ready shape
  have scalar : opcode.val ∉ Body.controlOpcodes := by
    simp only [Body.controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or] at ordinary ⊢
    have callNe : opcode.val ≠ 16 := fun h => call (UScalar.eq_of_val_eq h)
    have indirectNe : opcode.val ≠ 17 := fun h => indirect (UScalar.eq_of_val_eq h)
    tauto
  apply reader_scalar_reached _ st data env ctx index opcode compiler
    (fun state after => ObservedStack after state.vals.val) scalar
  intro capacity
  exact compiler_reader_total ops law compiler st.core data env ctx ready shape capacity opcode scalar
end Itasca.Compiler

end

end

/-! ## SafetyAndFinish -/

section

open Itasca.Representation

/-!
# Safety And Finish

Reached reader states preserve compiler safety and supply the final finish condition. These facts join replay invariants to successful body completion.
-/

/-! ## ReachedSafety -/

section

/-!
Normal return of a reader step at a reached compiler point.

Main declarations: `IndexedTableReaderCompilerPoint.reader_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPoint.reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial compiler types functions returns locals
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
    rw [Body.CallbackTrace.dispatch_br_table]
    apply compiler_table_reader_total ops law compiler _ data env pending.opened.shape.core
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
  · apply compiler_reader_ordinary_total ops law compiler ⟨{st.core with pos:=next}⟩ data env _ index opcode ready pending.opened.shape.core
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at control ⊢
    have tableNe : opcode.val ≠ 14 := fun h => table (UScalar.eq_of_val_eq h)
    tauto

end Itasca.Compiler

end

/-! ## IndexedCompilerInitial -/

section

/-!
Initial structured compiler state for body replay.

Main declarations: `StructuredReaderCompilerState.initial`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.initial {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) (types functions : List functype)
    (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType) (index : U32) (ft : Itasca.wasm_types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (compiled : StructuredCompilerPrefix jumpTables emit compiler compiler types functions (ft.results.val.map Translation.valueType) locals
      [] (SourceScope.initial (ft.results.val.map Translation.valueType)) [] 0) :
    StructuredReaderCompilerState jumpTables emit compiler compiler types functions (ft.results.val.map Translation.valueType) locals
      data env sourceLocals index ft (Body.initial index) []
      (SourceScope.initial (ft.results.val.map Translation.valueType)) []
      (Body.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨compiled, .initial data env sourceLocals index ft signature size,
    .initial (.TypeIndex index) 0#usize ft.params.val ft.results.val, ?_, .initial _, .initial _⟩
  exact ReaderReachability.initial _ _ _ _ rfl

end Itasca.Compiler

end

/-! ## IndexedPointNonempty -/

section

/-!
The complete reached reader likewise has an active source control frame.

Main declarations: `IndexedTableReaderCompilerPoint.ctrls_nonempty`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete reached reader likewise has an active source control frame. -/
theorem IndexedTableReaderCompilerPoint.ctrls_nonempty {A : Type}
    {emit initial compiler types functions returns locals data env sourceLocals index ft st}
    (point : @IndexedTableReaderCompilerPoint emit A initial compiler types functions returns locals data env sourceLocals index ft st) :
    st.core.ctrls.val ≠ [] := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := state.boundary.opened
  rw [controls]
  simp

end Itasca.Compiler

end

/-! ## IndexedCompilerFinish -/

section

/-!
The final executable check turns a completed actual body compilation into its retained source certificate, with the original function-start metadata.

Main declarations: `StructuredCompiledBody.finish`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The final executable check turns a completed actual body compilation into
its retained source certificate, with the original function-start metadata. -/
theorem StructuredCompiledBody.finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A}
    {emit types functions params declared results source}
    (body : StructuredCompiledBody final.function.jump_tables.val emit initial final types functions results (params ++ declared) source)
    (signature : types[initial.function.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (locals : initial.function.locals.val.map Translation.valueType = params ++ declared)
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
end Itasca.Compiler

end

end
