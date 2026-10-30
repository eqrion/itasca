import Itasca.Runtime.Compiler.Body.Reader.Publication.SourcePublicationAdvanceWasm2
import Itasca.Runtime.Compiler.Body.Reader.Checking.CheckedPrefixWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.ClosedInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceStepAcceptanceWasm2

/-!
Checked body-reader steps from the reached-source certificate through the typed body fold. SourceCheckedReachedBodyWasm2 carries the invariant between steps.
-/

/-! ## Source Checked Advance Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-paid executable and publication evidence, with all instruction checks retained. -/
def SourceCheckedReachedBodyWasm2 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourcePublicationReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st ∧
    CompilerInstructionPrefix compiler ∧ FrameExitSlotBounds compiler ∧
      (st.core.ctrls.val = [] → CheckedInstructionPrefix compiler.function)

/-- Every actual source-paid reader step retains all final checker obligations. -/
theorem source_checked_reader_advance_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st out : code.BodyState)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (allowance : ChargeCounter → Nat)
    (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter * (out.core.pos.val-st.core.pos.val))
    (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄)
    (coordinates : SourceCoordinates compiler) (maps : ControlMapPublication compiler)
    (targets : JumpTableBounds compiler)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (instructions : CompilerInstructionPrefix compiler) (exits : FrameExitSlotBounds compiler)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourceCheckedReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2.2 out ∧
        next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_publication_reader_advance_wasm2 ops law initial compiler C locals data env sourceLocals index ft st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures bodyBound nonempty next advance inbounds
    allowance paid acceptance coordinates maps targets extent
  obtain ⟨⟨reply,targetOut,after⟩,called,status,same,held,forward⟩ := WP.spec_imp_exists retained
  dsimp only at status same held forward
  subst reply targetOut
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have extentBefore : compiler.function.body_end.val = compiler.function.body_start.val+data.length := by
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := state.compiled.metadata.fields
    rw [start,finish]
    exact extent
  have checks := point.checked_prefix (ctx := ⟨sourceLocals,ft.results⟩) ops law C layout initialLocals initialCapacity localsMatch metadata
    matched contextLocals signatures extent bodyBound maps ledger.fixups instructions exits next advance inbounds out data.val[st.core.pos.val] rfl called
  have finalInstructions : out.core.ctrls.val = [] → CheckedInstructionPrefix after.function := by
    intro closed
    rcases point.advance_or_closing ops law C layout localsMatch metadata matched contextLocals signatures
      bodyBound next advance inbounds out called with ⟨ended,_⟩ | fresh
    · have callEnd : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2 11#u8 compiler =
            .ok (.Ok (),out,after) := by simpa only [ended] using called
      exact state.closed_checked_instructions (ctx := ⟨sourceLocals,ft.results⟩) ops law layout initialLocals initialCapacity extentBefore maps
        instructions exits next advance inbounds out closed ended callEnd
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,checks.1,checks.2,finalInstructions⟩,forward⟩

end Itasca.Runtime.Compiler

end

/-! ## Source Checked Steps Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Complete-profile Wasm 2 body steps retain executable, resource,
coordinate and control-map bounds together, including all SIMD forms. -/
theorem source_checked_body_steps_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
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

end Itasca.Runtime.Compiler

end
