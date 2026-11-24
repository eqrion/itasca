import Itasca.Runtime.Compiler.Body.Reader.Checking.SourceCheckedSteps
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay

/-!
Independent Wasm 2 body validity and source-only resource demand imply actual body acceptance with every final instruction check through the complete loop. Start bounds describe only the prepared prefix.

Main declarations: `compiler_body_checked_available`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independent Wasm 2 body validity and source-only resource demand imply
actual body acceptance with every final instruction check through the complete loop. Start bounds describe only the prepared prefix. -/
theorem compiler_body_checked_available {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (point : IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) initial initial
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (ft.results.val.map Translation.valueType) locals data env sourceLocals index ft (Body.initial index))
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger initial [])
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (body : Body.Validated data env sourceLocals index)
    (room : BodyResourceRoom initial data.length
      (independentBodyDemand data env ⟨sourceLocals,ft.results⟩ index).operands bound)
    (coordinates : SourceCoordinates initial) (maps : ControlMapPublication initial)
    (targets : JumpTableBounds initial)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (instructions : CompilerInstructionPrefix initial) (exits : FrameExitSlotBounds initial)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data
      env ⟨sourceLocals,ft.results⟩ index initial ⦃ result => result.1 = .Ok () ∧
        ∃ closed, SourceCheckedReachedBody initial C locals data env sourceLocals index ft result.2 closed ∧
          closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  refine independent_body_accepted_replay (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
     data env ⟨sourceLocals,ft.results⟩ index limits room.size body
    (fun st _ compiler => SourceCheckedReachedBody initial C locals data env sourceLocals index ft compiler st)
    initial ?_ ?_
  · intro st started
    have facts := code.initial_state.start env index
    rw [started,WP.spec_ok] at facts
    obtain ⟨rfl,_⟩ := facts
    refine ⟨⟨⟨.inr ⟨point,ledger⟩,?_⟩,coordinates,maps,targets,?_⟩,instructions,exits,?_⟩
    · simpa [Body.initial] using SourceCompilationBudget.initial initial.budget bodyResourceRate
    · intro closed
      simp [Body.initial] at closed
    · intro closed
      simp [Body.initial] at closed
  · exact source_checked_body_steps ops law bound allocation initial C locals data env sourceLocals index ft
      layout localsMatch metadata matched contextLocals signatures
      initialLocals initialCapacity
      (independentBodyLog data env ⟨sourceLocals,ft.results⟩ index) room extent

end Itasca.Compiler
