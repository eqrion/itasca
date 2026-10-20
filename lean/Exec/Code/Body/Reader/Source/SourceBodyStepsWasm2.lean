import Exec.Code.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Exec.Code.Body.Reader.Source.SourceBudgetAdvance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Instantiate the complete source-reference body-step refinement with actual
compiler acceptance and source-paid budget preservation. No accepted target
trace or per-opcode acceptance premise remains in this refinement theorem. -/
theorem source_budget_body_steps_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (final : List Observation)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound) :
    ReachedBody.AcceptingSuffixRefinement recorder (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ⟨sourceLocals,ft.results⟩ index .Wasm2 final
      (fun st _ compiler => SourceBudgetReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st) := by
  intro st before compiler held suffix nonempty inbounds next advance out after reference
  obtain ⟨reached,budget⟩ := held
  rcases reached with closed | ⟨point,ledger⟩
  · exact False.elim (nonempty closed)
  have acceptance := point.step_available_from_source ops law bound allocation localsMatch metadata signatures C matched
    ledger before after final out room budget nonempty next advance inbounds reference suffix
  exact source_budget_reader_advance_wasm2 ops law initial compiler C locals data env sourceLocals index ft st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures room.coordinate nonempty next advance inbounds
    (fun counter => bodyResourceRate counter*(out.core.pos.val-st.core.pos.val)) (by intro counter; rfl) acceptance

end Exec.Code
