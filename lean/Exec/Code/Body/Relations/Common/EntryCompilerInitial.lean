import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Body.Reader.Common.ReaderBoundary
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Common.ReaderBoundaryInitial
import Exec.Code.Body.Callbacks.Common.CompilerPrefixStart
import Exec.Code.Body.Relations.Common.FunctionStartFacts
import Exec.Code.Local.Relations.Common.EntryTypedSteps
namespace Itasca.Runtime.Code
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

theorem TypedRunWasm2.body_size {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after} (run : TypedRunWasm2 visitor data env ctx index st before after) :
    data.length ≤ limits.MAX_FUNCTION_BYTES.val := by
  cases run with
  | done typed _ _ => exact typed.bounds.size
  | step typed _ _ _ _ _ => exact typed.bounds.size

end Itasca.Runtime.Code
