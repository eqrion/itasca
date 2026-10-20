import Exec.Code.Body.Reader.Source.SourceBudgetAdvanceWasm1
import Exec.Code.Body.Reader.Publication.ReaderPublicationWasm1

import Exec.Code.Body.Control.Common.IndexedClosingWitness
import Exec.Code.Body.Reader.Common.IndexedPointNonempty
import Exec.Code.Body.Reader.Control.ReaderRootMapPublication

import Exec.Code.Body.Reader.Checking.ReaderJumpTargets

import Exec.Code.Local.Publication.FunctionPublicationRanges

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source-paid body progress together with publication-coordinate and map bounds. -/
def SourcePublicationReachedBodyWasm1 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourceBudgetReachedBodyWasm1 initial C data env ctx compiler st ∧
    SourceCoordinates compiler ∧ ControlMapPublication compiler ∧ JumpTableBounds compiler ∧
      (st.core.ctrls.val = [] → FinalControlMapBounds compiler.function ∧ SourceAligned compiler)

/-- Closing the retained body exposes the exact final map checker bounds. -/
theorem SourcePublicationReachedBodyWasm1.final_bounds {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {C data env ctx st}
    (held : SourcePublicationReachedBodyWasm1 initial C data env ctx compiler st)
    (closed : st.core.ctrls.val = []) :
    SourceCoordinates compiler ∧ FinalControlMapBounds compiler.function :=
  ⟨held.2.1,(held.2.2.2.2 closed).1⟩

/-- All source and target range checks at the actual completed function. -/
theorem SourcePublicationReachedBodyWasm1.final_ranges {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {C data env ctx st}
    (held : SourcePublicationReachedBodyWasm1 initial C data env ctx compiler st)
    (closed : st.core.ctrls.val = []) : FunctionPublicationRanges compiler.function :=
  ⟨(held.2.2.2.2 closed).2,held.2.1.checker,(held.2.2.2.2 closed).1,held.2.2.2.1⟩

/-- Retain both publication invariants through an actual source-paid Wasm 1
reader step, alongside the existing executable prefix and resource ledger. -/
theorem source_publication_reader_advance_wasm1 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (st out : code.BodyState)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) (ctx.locals.val.map Translate.valueType)
      data env ctx (Wasm1.Loop.initialBlockType ctx.results.val) st.core)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS=ctx.locals.val.map Translate.valueType)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes (Wasm1.Loop.initialBlockType ctx.results.val) = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (allowance : ChargeCounter → Nat)
    (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter * (out.core.pos.val-st.core.pos.val))
    (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm1 data.val[st.core.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄)
    (coordinates : SourceCoordinates compiler) (maps : ControlMapPublication compiler)
    (targets : JumpTableBounds compiler)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm1 data.val[st.core.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourcePublicationReachedBodyWasm1 initial C data env ctx result.2.2 out ∧ next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_budget_reader_advance_wasm1 ops law initial compiler C data env ctx index st out point
    ledger budget layout localsMatch metadata matched contextLocals signatures bodyResults bodyBound next advance inbounds
    allowance paid acceptance
  obtain ⟨⟨reply,targetOut,after⟩,called,status,same,held,forward⟩ := WP.spec_imp_exists retained
  dsimp only at status same held forward
  subst reply targetOut
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have raw := profile_raw_success_wasm1 _ _ out data env ctx index _ compiler after called
  have extentBefore : compiler.function.body_end.val = compiler.function.body_start.val+data.length := by
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := state.compiled.metadata.fields
    rw [start,finish]
    exact extent
  have publication := reader_publication_wasm1 pending ops law _ compiler after out.core _ _ _ _ parents current
    state.compiled state.reach coordinates maps extentBefore raw
  have targetBounds := reader_jump_targets_wasm1 pending ops law compiler after out.core targets raw
  have finalMaps : out.core.ctrls.val = [] → FinalControlMapBounds after.function ∧ SourceAligned after := by
    intro closed
    rcases point.advance_or_closing ops law C layout localsMatch metadata matched contextLocals signatures
      bodyResults bodyBound next advance inbounds out.core raw with ⟨ended,_⟩ | fresh
    · have rawEnd : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          {st.core with pos := next} data env ctx 11#u8 compiler = .ok (.Ok (),out.core,after) := by
        simpa only [ended] using raw
      exact reader_root_map_publication_wasm1 pending ops law _ compiler after out.core _ _ _ _ parents current
        state.compiled state.sources maps extentBefore closed (by simpa only [pending,ReaderBoundaryWasm1.pending,global_simps] using ended)
        (by simpa only [global_simps] using rawEnd)
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,publication.1,publication.2,targetBounds,finalMaps⟩,forward⟩

end Exec.Code
