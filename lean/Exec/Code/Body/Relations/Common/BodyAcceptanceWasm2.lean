import Exec.Code.Body.Reader.Source.SourceBodyStepsWasm2
import Exec.Code.Local.Capacity.IndependentBodyReplay

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Complete Wasm 2 body acceptance from independent body validity, a prepared
function-start prefix, and source-only allocation/resource demand. The source
reference run is constructed internally by validator completeness. Every body
step and its resource preservation are derived, with no accepted target trace
or completed function certificate supplied by the caller. -/
theorem compiler_body_wasm2_available {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial initial
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft (Wasm2.initial index))
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger initial [])
    (signature : env.types.val[index.val]? = some ft)
    (environment : Profile.Environment .Wasm2 env) (limits : Profile.EnvironmentWithinLimits .Wasm2 env)
    (body : Profile.Body .Wasm2 data env sourceLocals index)
    (room : BodyResourceRoom initial data.length
      (independentBodyDemand .Wasm2 data env ⟨sourceLocals,ft.results⟩ index).operands bound) :
    CodeEntry.runBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) .Wasm2
      data env ⟨sourceLocals,ft.results⟩ index initial ⦃ result => result.1 = .Ok () ∧
        ∃ closed, SourceBudgetReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2 closed ∧
          closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  refine independent_body_accepted_replay (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    .Wasm2 data env ⟨sourceLocals,ft.results⟩ index ft signature rfl environment limits room.size body
    (fun st _ compiler => SourceBudgetReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st)
    initial ?_ ?_
  · intro st started
    have facts := code.initial_state.wasm2_start env ⟨sourceLocals,ft.results⟩ index
    rw [started,WP.spec_ok] at facts
    obtain ⟨rfl,_⟩ := facts
    refine ⟨.inr ⟨point,ledger⟩,?_⟩
    simpa [Wasm2.initial] using SourceCompilationBudget.initial initial.budget bodyResourceRate
  · exact source_budget_body_steps_wasm2 ops law bound allocation initial C locals data env sourceLocals index ft
      layout localsMatch metadata matched contextLocals signatures
      (independentBodyLog .Wasm2 data env ⟨sourceLocals,ft.results⟩ index) room

end Exec.Code
