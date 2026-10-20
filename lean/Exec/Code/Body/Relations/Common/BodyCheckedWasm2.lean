import Exec.Code.Body.Reader.Checking.SourceCheckedStepsWasm2
import Exec.Code.Local.Capacity.IndependentBodyReplay

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent Wasm 2 body validity and source-only resource demand imply
actual body acceptance with every final instruction check through the complete loop. Start bounds describe only the prepared prefix. -/
theorem compiler_body_wasm2_checked_available {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
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
      (independentBodyDemand .Wasm2 data env ⟨sourceLocals,ft.results⟩ index).operands bound)
    (coordinates : SourceCoordinates initial) (maps : ControlMapPublication initial)
    (targets : JumpTableBounds initial)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (instructions : CompilerInstructionPrefix initial) (exits : FrameExitSlotBounds initial)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    CodeEntry.runBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) .Wasm2
      data env ⟨sourceLocals,ft.results⟩ index initial ⦃ result => result.1 = .Ok () ∧
        ∃ closed, SourceCheckedReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2 closed ∧
          closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  refine independent_body_accepted_replay (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    .Wasm2 data env ⟨sourceLocals,ft.results⟩ index ft signature rfl environment limits room.size body
    (fun st _ compiler => SourceCheckedReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st)
    initial ?_ ?_
  · intro st started
    have facts := code.initial_state.wasm2_start env ⟨sourceLocals,ft.results⟩ index
    rw [started,WP.spec_ok] at facts
    obtain ⟨rfl,_⟩ := facts
    refine ⟨⟨⟨.inr ⟨point,ledger⟩,?_⟩,coordinates,maps,targets,?_⟩,instructions,exits,?_⟩
    · simpa [Wasm2.initial] using SourceCompilationBudget.initial initial.budget bodyResourceRate
    · intro closed
      simp [Wasm2.initial] at closed
    · intro closed
      simp [Wasm2.initial] at closed
  · exact source_checked_body_steps_wasm2 ops law bound allocation initial C locals data env sourceLocals index ft
      layout localsMatch metadata matched contextLocals signatures
      initialLocals initialCapacity
      (independentBodyLog .Wasm2 data env ⟨sourceLocals,ft.results⟩ index) room extent

end Exec.Code
