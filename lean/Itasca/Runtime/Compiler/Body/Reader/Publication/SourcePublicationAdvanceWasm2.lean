import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.Runtime.Compiler.Body.Reader.Publication.PublicationWasm2

import Itasca.Runtime.Compiler.Body.Control.Closing.IndexedClosingWitness
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPointNonempty
import Itasca.Runtime.Compiler.Body.Reader.Control.RootMapPublication

import Itasca.Runtime.Compiler.Body.Reader.Checking.JumpTargets

import Itasca.Runtime.Compiler.Local.Publication.FunctionPublicationRanges

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Reached Wasm 2 executable and resource evidence with both publication invariants. -/
def SourcePublicationReachedBodyWasm2 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : module.Env)
    (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourceBudgetReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st ∧
    SourceCoordinates compiler ∧ ControlMapPublication compiler ∧ JumpTableBounds compiler ∧
      (st.core.ctrls.val = [] → FinalControlMapBounds compiler.function ∧ SourceAligned compiler)

/-- All source and target range checks at the actual complete-profile function. -/
theorem SourcePublicationReachedBodyWasm2.final_ranges {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {C locals data env sourceLocals index ft st}
    (held : SourcePublicationReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st)
    (closed : st.core.ctrls.val = []) : FunctionPublicationRanges compiler.function :=
  ⟨(held.2.2.2.2 closed).2,held.2.1.checker,(held.2.2.2.2 closed).1,held.2.2.2.1⟩

/-- Actual source-paid Wasm 2 reader progress retains executable, resource,
source-coordinate, and control-map bounds together. -/
theorem source_publication_reader_advance_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
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
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourcePublicationReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2.2 out ∧
        next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_budget_reader_advance_wasm2 ops law initial compiler C locals data env sourceLocals index ft st out point
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
  have publication := reader_publication_wasm2 pending ops law _ compiler after out ⟨sourceLocals,ft.results⟩
    _ _ _ _ parents current state.compiled state.reach signaturesBefore coordinates maps extentBefore called
  have targetBounds := reader_jump_targets_wasm2 pending ops law compiler after out ⟨sourceLocals,ft.results⟩ targets called
  have finalMaps : out.core.ctrls.val = [] → FinalControlMapBounds after.function ∧ SourceAligned after := by
    intro closed
    rcases point.advance_or_closing ops law C layout localsMatch metadata matched contextLocals signatures
      bodyBound next advance inbounds out called with ⟨ended,_⟩ | fresh
    · have callEnd : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2 11#u8 compiler =
            .ok (.Ok (),out,after) := by simpa only [ended] using called
      exact reader_root_map_publication_wasm2 pending ops law _ compiler after out ⟨sourceLocals,ft.results⟩
        _ _ _ _ parents current state.compiled state.sources maps extentBefore closed ended callEnd
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,publication.1,publication.2,targetBounds,finalMaps⟩,forward⟩

end Itasca.Runtime.Code
