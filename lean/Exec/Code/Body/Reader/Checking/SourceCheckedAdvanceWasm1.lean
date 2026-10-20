import Exec.Code.Body.Reader.Publication.SourcePublicationAdvanceWasm1
import Exec.Code.Body.Reader.Checking.ReaderCheckedPrefixWasm1
import Exec.Code.Body.Reader.Control.ReaderClosedInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source-paid executable and publication evidence, with all instruction checks retained. -/
def SourceCheckedReachedBodyWasm1 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  SourcePublicationReachedBodyWasm1 initial C data env ctx compiler st ∧
    CompilerInstructionPrefix compiler ∧ FrameExitSlotBounds compiler ∧
      (st.core.ctrls.val = [] → CheckedInstructionPrefix compiler.function)

/-- Every actual source-paid reader step retains all final checker obligations. -/
theorem source_checked_reader_advance_wasm1 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
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
    (initialLocals : compilerLocals initial = ctx.locals.val.map Translate.valueType)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (instructions : CompilerInstructionPrefix compiler) (exits : FrameExitSlotBounds compiler)
    (extent : initial.function.body_end.val = initial.function.body_start.val+data.length) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm1 data.val[st.core.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourceCheckedReachedBodyWasm1 initial C data env ctx result.2.2 out ∧ next.val ≤ out.core.pos.val ⦄ := by
  have retained := source_publication_reader_advance_wasm1 ops law initial compiler C data env ctx index st out
    point ledger budget layout localsMatch metadata matched contextLocals signatures bodyResults bodyBound next advance inbounds
    allowance paid acceptance coordinates maps targets extent
  obtain ⟨⟨reply,targetOut,after⟩,called,status,same,held,forward⟩ := WP.spec_imp_exists retained
  dsimp only at status same held forward
  subst reply targetOut
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have extentBefore : compiler.function.body_end.val = compiler.function.body_start.val+data.length := by
    obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := state.compiled.metadata.fields
    rw [start,finish]
    exact extent
  have raw := profile_raw_success_wasm1 _ _ out data env ctx index _ compiler after called
  have checks := point.checked_prefix ops law C bodyResults layout initialLocals initialCapacity localsMatch metadata
    matched contextLocals signatures extent bodyBound maps ledger.fixups instructions exits next advance inbounds out.core data.val[st.core.pos.val] rfl raw
  have finalInstructions : out.core.ctrls.val = [] → CheckedInstructionPrefix after.function := by
    intro closed
    rcases point.advance_or_closing ops law C layout localsMatch metadata matched contextLocals signatures
      bodyResults bodyBound next advance inbounds out.core raw with ⟨ended,_⟩ | fresh
    · have callEnd : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          {st.core with pos := next} data env ctx 11#u8 compiler = .ok (.Ok (),out.core,after) := by
        simpa only [ended] using raw
      exact state.closed_checked_instructions ops law bodyResults layout initialLocals initialCapacity extentBefore maps
        instructions exits next advance inbounds out.core closed ended callEnd
    · exact False.elim (fresh.ctrls_nonempty closed)
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,after),called,rfl,rfl,⟨held,checks.1,checks.2,finalInstructions⟩,forward⟩

end Exec.Code
