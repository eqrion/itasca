import Exec.Code.Body.Reader.Acceptance.SourceStepAcceptanceWasm1
import Exec.Code.Body.Reader.Publication.SourcePublicationAdvanceWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual complete-profile Wasm 1 body steps retain source-paid resource,
executable-prefix, coordinate, and control-map invariants together. -/
theorem source_publication_body_steps_wasm1 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS=ctx.locals.val.map Translate.valueType)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes (Wasm1.Loop.initialBlockType ctx.results.val) = ctx.results.val.map Translate.valueType)
    (final : List Observation)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    ReachedBody.AcceptingSuffixRefinement recorder (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx index .Wasm1 final
      (fun st _ compiler => SourcePublicationReachedBodyWasm1 initial C data env ctx compiler st) := by
  intro st before compiler held suffix nonempty inbounds next advance out after reference
  obtain ⟨⟨reached,budget⟩,coordinates,maps,targets,finalMaps⟩ := held
  rcases reached with closed | ⟨point,ledger⟩
  · exact False.elim (nonempty closed)
  have acceptance := point.step_available_from_source ops law bound allocation localsMatch metadata signatures bodyResults C matched
    ledger before after final out room budget index nonempty next advance inbounds reference suffix
  exact source_publication_reader_advance_wasm1 ops law initial compiler C data env ctx index st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures bodyResults room.coordinate next advance inbounds
    (fun counter => bodyResourceRate counter*(out.core.pos.val-st.core.pos.val)) (by intro counter; rfl) acceptance coordinates maps targets extent

end Exec.Code
