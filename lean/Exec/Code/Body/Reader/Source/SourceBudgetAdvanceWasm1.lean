import Exec.Code.Body.Relations.Common.ReachedBodyWasm1
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptanceWasm1
import Exec.Code.Local.Capacity.BodyResourceRoom

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source geometry and compiler ledgers retained at each Wasm 1 body boundary,
together with all resource counters paid by consumed source bytes. -/
def SourceBudgetReachedBodyWasm1 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  (st.core.ctrls.val = [] ∨
    (IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) (ctx.locals.val.map Translate.valueType)
      data env ctx (Wasm1.Loop.initialBlockType ctx.results.val) st.core ∧
      ReachedCompilerLedger compiler st.core.vals.val)) ∧
    SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val

/-- A source-paid Wasm 1 accepted step retains both executable prefix evidence
and the resource ledger needed for the next instruction. -/
theorem source_budget_reader_advance_wasm1 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
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
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm1 data.val[st.core.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourceBudgetReachedBodyWasm1 initial C data env ctx result.2.2 out ∧ next.val ≤ out.core.pos.val ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have names := OrdinaryNamespaces.of_initial layout localsMatch metadata signatures
  obtain ⟨⟨reply,targetOut,after⟩,called,accepted,same,effect⟩ := WP.spec_imp_exists acceptance
  dsimp only at accepted same effect
  subst reply targetOut
  have normal := point.reader_total ops law names ledger bodyBound index next advance inbounds data.val[st.core.pos.val]
  rw [called,WP.spec_ok] at normal
  have raw := profile_raw_success_wasm1 _ _ out data env ctx index _ compiler after called
  have forward : next.val ≤ out.core.pos.val := (pending.accepted_after _ compiler after out.core raw).2.1
  have fresh := ledger.reader_wasm1 ops law pending out.core (normal rfl) raw
  have moved := point.advance_or_closed ops law C layout localsMatch metadata matched contextLocals signatures
    bodyResults bodyBound next advance inbounds out.core raw
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,after),called,rfl,rfl,⟨?_,?_⟩,forward⟩
  · rcases moved with closed | point'
    · exact .inl closed
    · exact .inr ⟨point',fresh⟩
  · exact budget.advance effect (by omega) paid

end Exec.Code
