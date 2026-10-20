import Exec.Code.Body.Reader.Source.SourceBodyStepsWasm1
import Exec.Code.Local.Capacity.IndependentBodyReplay

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Complete Wasm 1 body acceptance from independent body validity, a prepared
function-start prefix, and source-only resource demand. Validator completeness
constructs the source run internally; no accepted target trace or completed
function certificate is required. -/
theorem compiler_body_wasm1_available {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (ft : types.FuncType)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial initial
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) (ctx.locals.val.map Translate.valueType)
      data env ctx (Wasm1.Loop.initialBlockType ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)))
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS=ctx.locals.val.map Translate.valueType)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes (Wasm1.Loop.initialBlockType ctx.results.val) = ctx.results.val.map Translate.valueType)
    (ledger : ReachedCompilerLedger initial [])
    (signature : env.types.val[index.val]? = some ft) (results : ctx.results.val = ft.results.val)
    (environment : Profile.Environment .Wasm1 env) (limits : Profile.EnvironmentWithinLimits .Wasm1 env)
    (body : Profile.Body .Wasm1 data env ctx.locals index)
    (room : BodyResourceRoom initial data.length
      (independentBodyDemand .Wasm1 data env ctx index).operands bound) :
    CodeEntry.runBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) .Wasm1
      data env ctx index initial ⦃ result => result.1 = .Ok () ∧
        ∃ closed, SourceBudgetReachedBodyWasm1 initial C data env ctx result.2 closed ∧
          closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  refine independent_body_accepted_replay (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    .Wasm1 data env ctx index ft signature results environment limits room.size body
    (fun st _ compiler => SourceBudgetReachedBodyWasm1 initial C data env ctx compiler st) initial ?_ ?_
  · intro st started
    rw [code.initial_state,code.start_function.raw_spec] at started
    simp only [bind_ok,core.result.Result.Ok.injEq,Result.ok.injEq] at started
    subst st
    refine ⟨.inr ⟨?_,?_⟩,?_⟩
    · simpa [alloc.vec.Vec.deref] using point
    · simpa [alloc.vec.Vec.deref,Wasm1.Loop.initial] using ledger
    · simpa [Wasm1.Loop.initial] using SourceCompilationBudget.initial initial.budget bodyResourceRate
  · exact source_budget_body_steps_wasm1 ops law bound allocation initial C data env ctx 0#u32
      layout localsMatch metadata matched contextLocals signatures bodyResults
      (independentBodyLog .Wasm1 data env ctx index) room

end Exec.Code
