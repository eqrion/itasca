import Itasca.Runtime.Compiler.Body.Reader.Replay.SingleCallback
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedControlAcceptance
import Itasca.Visitor.BodyReplay
import Itasca.Body.Trace.BytesDispatch
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.Runtime.Compiler.Body.Control.Closing
import Itasca.Runtime.Compiler.Body.Reader.Replay.SafetyAndFinish
import Itasca.Runtime.Compiler.Body.Reader.Checking.CheckedPrefix
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundAcceptance

/-!
Proofs for Runtime / Compiler / Body / Reader / Checking.

This module collects SourcePublicationAdvance, SourceCheckedSteps.
Each section documents its contracts and consumers.
-/

/-! ## SourcePublicationAdvance -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Publication.

This module collects Publication, SourcePublicationAdvance.
Each section documents its contracts and consumers.
-/

/-! ## Publication -/

section

/-!
Every accepted Wasm 2 reader step preserves both publication invariants from its source-typed reached prefix, including unreachable code and every complete callback family.

Main declarations: `reader_publication`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace Itasca.Body
set_option maxRecDepth 4096

/-- Every accepted Wasm 2 reader step preserves both publication invariants
from its source-typed reached prefix, including unreachable code and every
complete callback family. -/
theorem reader_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases h2 : opcode = 2#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 2#u8 before = .ok (.Ok (),out,after) := by simpa only [← h2] using accepted
    exact reader_enter_publication p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .block (.inl rfl) h2 call
  by_cases h3 : opcode = 3#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 3#u8 before = .ok (.Ok (),out,after) := by simpa only [← h3] using accepted
    exact reader_enter_publication p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .loop (.inr (.inl rfl)) h3 call
  by_cases h4 : opcode = 4#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 4#u8 before = .ok (.Ok (),out,after) := by simpa only [← h4] using accepted
    exact reader_enter_publication p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .then_ (.inr (.inr rfl)) h4 call
  by_cases h11 : opcode = 11#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 11#u8 before = .ok (.Ok (),out,after) := by simpa only [← h11] using accepted
    exact reader_end_publication p ops law initial before after out ctx types functions returns locals parents current
      invariant coordinates maps extent h11 call
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by
    have cursor := invariant.cursor
    have bounded := p.inbounds
    change p.start.val < data.length at bounded
    omega
  let sourceState : code.BodyState := {core := {st.core with pos := p.start}}
  have nonempty : sourceState.core.ctrls.val ≠ [] := by
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    change st.core.ctrls.val ≠ []
    rw [controls]
    simp
  have progress := code.step_profile.accepted_progress
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index sourceState out before after
    p.size ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩ (by simp [sourceState]) p.ctrls nonempty p.inbounds st.core.pos p.pos accepted
  have forward : before.next_source.val ≤ out.core.pos.val := by
    have cursor := invariant.cursor
    have position := p.pos
    omega
  by_cases h14 : opcode = 14#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 14#u8 before = .ok (.Ok (),out,after) := by simpa only [← h14] using accepted
    rw [CallbackTrace.dispatch_br_table] at call
    exact reader_table_publication ops law before after st out data env coordinates maps inside forward call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by
    simp only [global_simps]
    tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_body_callback
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after blocked accepted
  exact compiler_non_scope_hook_publication ops law before after out.core
    (.of_range action range ordinary) coordinates maps inside forward callback

end Itasca.Compiler

end

/-! ## SourcePublicationAdvance -/

section

/-!
# Publication through source advancement

Reached executable/resource evidence retains both source-coordinate and control-map publication invariants. Advancing an actual reader step preserves those bounds.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Reached Wasm 2 executable and resource evidence with both publication invariants. -/
def SourcePublicationReachedBody {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourceBudgetReachedBody initial C locals data env sourceLocals index ft compiler st ∧
    SourceCoordinates compiler ∧ ControlMapPublication compiler ∧ JumpTableBounds compiler ∧
      (st.core.ctrls.val = [] → FinalControlMapBounds compiler.function ∧ SourceAligned compiler)

/-- All source and target range checks at the actual complete function. -/
theorem SourcePublicationReachedBody.final_ranges {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {C locals data env sourceLocals index ft st}
    (held : SourcePublicationReachedBody initial C locals data env sourceLocals index ft compiler st)
    (closed : st.core.ctrls.val = []) : FunctionPublicationRanges compiler.function :=
  ⟨(held.2.2.2.2 closed).2,held.2.1.checker,(held.2.2.2.2 closed).1,held.2.2.2.1⟩

/-- Actual source-paid Wasm 2 reader progress retains executable, resource,
source-coordinate, and control-map bounds together. -/
theorem source_publication_reader_advance {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st out : code.BodyState)
    (point : IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (ft.results.val.map Translation.valueType) locals data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (allowance : ChargeCounter → Nat)
    (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter * (out.core.pos.val-st.core.pos.val))
    (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄)
    (coordinates : SourceCoordinates compiler) (maps : ControlMapPublication compiler)
    (targets : JumpTableBounds compiler)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourcePublicationReachedBody initial C locals data env sourceLocals index ft result.2.2 out ∧
        next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_budget_reader_advance ops law initial compiler C locals data env sourceLocals index ft st out point
    ledger budget layout localsMatch metadata matched contextLocals signatures bodyBound nonempty next advance inbounds allowance paid acceptance
  obtain ⟨⟨reply,targetOut,after⟩,called,status,same,held,forward⟩ := WP.spec_imp_exists retained
  dsimp only at status same held forward
  subst reply targetOut
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have extentBefore : compiler.function.body_end.val = compiler.function.body_start.val+data.length := by
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := state.compiled.metadata.fields
    rw [start,finish]
    exact extent
  have signaturesBefore : SignatureSequence compiler.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  have publication := reader_publication pending ops law _ compiler after out ⟨sourceLocals,ft.results⟩
    _ _ _ _ parents current state.compiled state.reach signaturesBefore coordinates maps extentBefore called
  have targetBounds := reader_jump_targets pending ops law compiler after out ⟨sourceLocals,ft.results⟩ targets called
  have finalMaps : out.core.ctrls.val = [] → FinalControlMapBounds after.function ∧ SourceAligned after := by
    intro closed
    rcases point.advance_or_closing ops law C layout localsMatch metadata matched contextLocals signatures
      bodyBound next advance inbounds out called with ⟨ended,_⟩ | fresh
    · have callEnd : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index 11#u8 compiler =
            .ok (.Ok (),out,after) := by simpa only [ended] using called
      exact reader_root_map_publication pending ops law _ compiler after out ⟨sourceLocals,ft.results⟩
        _ _ _ _ parents current state.compiled state.sources maps extentBefore closed ended callEnd
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,publication.1,publication.2,targetBounds,finalMaps⟩,forward⟩

end Itasca.Compiler

end

end

/-! ## SourceCheckedSteps -/

section

/-!
Checked body-reader steps from the reached-source certificate through the typed body fold. SourceCheckedReachedBody carries the invariant between steps.
-/

/-! ## Source Checked Advance Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-paid executable and publication evidence, with all instruction checks retained. -/
def SourceCheckedReachedBody {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : metadata.Env)
    (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourcePublicationReachedBody initial C locals data env sourceLocals index ft compiler st ∧
    CompilerInstructionPrefix compiler ∧ FrameExitSlotBounds compiler ∧
      (st.core.ctrls.val = [] → CheckedInstructionPrefix compiler.function)

/-- Every actual source-paid reader step retains all final checker obligations. -/
theorem source_checked_reader_advance {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st out : code.BodyState)
    (point : IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (ft.results.val.map Translation.valueType) locals data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (allowance : ChargeCounter → Nat)
    (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter * (out.core.pos.val-st.core.pos.val))
    (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄)
    (coordinates : SourceCoordinates compiler) (maps : ControlMapPublication compiler)
    (targets : JumpTableBounds compiler)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (instructions : CompilerInstructionPrefix compiler) (exits : FrameExitSlotBounds compiler)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourceCheckedReachedBody initial C locals data env sourceLocals index ft result.2.2 out ∧
        next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_publication_reader_advance ops law initial compiler C locals data env sourceLocals index ft st out
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
          {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index 11#u8 compiler =
            .ok (.Ok (),out,after) := by simpa only [ended] using called
      exact state.closed_checked_instructions (ctx := ⟨sourceLocals,ft.results⟩) ops law layout initialLocals initialCapacity extentBefore maps
        instructions exits next advance inbounds out closed ended callEnd
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,checks.1,checks.2,finalInstructions⟩,forward⟩

end Itasca.Compiler

end

/-! ## Source Checked Steps Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Complete body steps retain executable, resource,
coordinate and control-map bounds together, including all SIMD forms. -/
theorem source_checked_body_steps {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (final : List Observation)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    Visitor.Replay.ReachedBody.AcceptingSuffixRefinement recorder (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ⟨sourceLocals,ft.results⟩ index final
      (fun st _ compiler => SourceCheckedReachedBody initial C locals data env sourceLocals index ft compiler st) := by
  intro st before compiler held suffix nonempty inbounds next advance out after reference
  obtain ⟨publication,instructions,exits,finalInstructions⟩ := held
  obtain ⟨⟨reached,budget⟩,coordinates,maps,targets,finalMaps⟩ := publication
  rcases reached with closed | ⟨point,ledger⟩
  · exact False.elim (nonempty closed)
  have acceptance := point.step_available_from_source ops law bound allocation localsMatch metadata signatures C matched
    ledger before after final out room budget nonempty next advance inbounds reference suffix
  exact source_checked_reader_advance ops law initial compiler C locals data env sourceLocals index ft st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures room.coordinate nonempty next advance inbounds
    (fun counter => bodyResourceRate counter*(out.core.pos.val-st.core.pos.val)) (by intro counter; rfl) acceptance coordinates maps targets initialLocals initialCapacity instructions exits extent

end Itasca.Compiler

end

end
