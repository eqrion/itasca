import Exec.Code.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Exec.Code.Body.Reader.Checking.SourceCheckedAdvanceWasm2

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Complete-profile Wasm 2 body steps retain executable, resource,
coordinate and control-map bounds together, including all SIMD forms. -/
theorem source_checked_body_steps_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (final : List Observation)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    ReachedBody.AcceptingSuffixRefinement recorder (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ⟨sourceLocals,ft.results⟩ index .Wasm2 final
      (fun st _ compiler => SourceCheckedReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st) := by
  intro st before compiler held suffix nonempty inbounds next advance out after reference
  obtain ⟨publication,instructions,exits,finalInstructions⟩ := held
  obtain ⟨⟨reached,budget⟩,coordinates,maps,targets,finalMaps⟩ := publication
  rcases reached with closed | ⟨point,ledger⟩
  · exact False.elim (nonempty closed)
  have acceptance := point.step_available_from_source ops law bound allocation localsMatch metadata signatures C matched
    ledger before after final out room budget nonempty next advance inbounds reference suffix
  exact source_checked_reader_advance_wasm2 ops law initial compiler C locals data env sourceLocals index ft st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures room.coordinate nonempty next advance inbounds
    (fun counter => bodyResourceRate counter*(out.core.pos.val-st.core.pos.val)) (by intro counter; rfl) acceptance coordinates maps targets initialLocals initialCapacity instructions exits extent

end Itasca.Runtime.Code
