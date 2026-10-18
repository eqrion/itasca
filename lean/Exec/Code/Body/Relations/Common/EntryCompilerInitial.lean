import Exec.Code.Body.Reader.Common.ReaderCompilerInitial
import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Relations.Common.FunctionStartFacts
import Exec.Code.Local.Relations.Common.EntryTypedSteps
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Lookup in the canonical source table selects an actual captured compiler
signature, including exact parameter and result widths. -/
theorem SignatureSequence.lookup_source {signatures types}
    (sequence : SignatureSequence signatures types) {index : Nat} {ty : Itasca.types.FuncType}
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
    (env : module.Env) (ctx : code.Context) (index : U32) (ft : types.FuncType)
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
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
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

theorem TypedRunWasm1.body_size {V : Type} {visitor : code.OpVisitor V}
    {data env ctx bt st before after} (run : TypedRunWasm1 visitor data env ctx bt st before after) :
    data.length ≤ limits.MAX_FUNCTION_BYTES.val := by
  cases run with
  | done typed _ _ => exact typed.bounds.size
  | step typed _ _ _ _ _ => exact typed.bounds.size

theorem TypedRunWasm2.body_size {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after} (run : TypedRunWasm2 visitor data env ctx index st before after) :
    data.length ≤ limits.MAX_FUNCTION_BYTES.val := by
  cases run with
  | done typed _ _ => exact typed.bounds.size
  | step typed _ _ _ _ _ => exact typed.bounds.size

theorem witness_compiler_initial_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm2)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    ReaderCompilerPointWasm2 w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) ∧
    TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState final := by
  obtain ⟨facts, compiled⟩ := witness_compiler_start ops law w signatureTable functionTable endFits created
  have run := witness_typed_steps w
  change TypedRunWasm2 _ _ _ _ _ _ _ _ at run
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  exact ⟨facts, (ReaderCompilerStateWasm2.initial _ _ _ _ _ _ _ _ _ lookup run.body_size compiled).point, run⟩

theorem witness_compiler_initial_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm1)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (singleResult : w.ft.results.val.length ≤ 1) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    Control.resultTypes (Wasm1.Loop.initialBlockType w.ctx.results.val) = w.ctx.results.val.map Translate.valueType ∧
    ReaderCompilerPointWasm1 w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ctx.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx (Wasm1.Loop.initialBlockType w.ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType w.ctx.results.val)) ∧
    TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx (Wasm1.Loop.initialBlockType w.ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType w.ctx.results.val)) w.startedState final := by
  obtain ⟨facts, compiled⟩ := witness_compiler_start ops law w signatureTable functionTable endFits created
  have run := witness_typed_steps w
  change TypedRunWasm1 _ _ _ _ _ _ _ _ at run
  obtain ⟨bt, results⟩ := CodeEntry.blockType_of_length w.ft.results.val singleResult
  have initialBt : Wasm1.Loop.initialBlockType w.ctx.results.val = bt := by
    rw [w.context_results, results, Wasm1.Loop.initialBlockType_results]
  have returns : Control.resultTypes (Wasm1.Loop.initialBlockType w.ctx.results.val) =
      w.ctx.results.val.map Translate.valueType := by
    rw [initialBt, w.context_results, results]
    rfl
  have state := ReaderCompilerStateWasm1.initial w.startedState
    (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
    (w.ctx.locals.val.map Translate.valueType) w.body env w.ctx
    (Wasm1.Loop.initialBlockType w.ctx.results.val) run.body_size
    (by rw [returns, w.context_results]; exact compiled)
  rw [returns] at state
  exact ⟨facts, returns, state.point, run⟩
end Exec.Code
