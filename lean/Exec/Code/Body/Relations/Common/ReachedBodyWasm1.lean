import Exec.Code.Body.Reader.Common.ReachedReaderSafety
import Exec.Code.Body.Control.Common.IndexedAdvanceOrClosed
import Itasca.Visitor.ReaderAcceptedProgress
import Itasca.Visitor.InvariantBodyLoop
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

private theorem profile_wasm1_raw {V} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (accepted : code.step_profile visitor st data env ctx index .Wasm1 opcode before = .ok (.Ok (),out,after)) :
    code.step visitor st.core data env ctx opcode before = .ok (.Ok (),out.core,after) := by
  unfold code.step_profile at accepted
  obtain ⟨⟨reply,state,changed⟩,run,rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry,Result.ok.injEq,Prod.mk.injEq] at rest
  obtain ⟨replyEq,states,changedEq⟩ := rest
  rw [replyEq,changedEq] at run
  have coreEq := congrArg code.BodyState.core states
  dsimp only at coreEq
  simpa only [coreEq] using run

/-- The extracted Wasm 1 body validator returns on arbitrary remaining bytes
from the canonical fresh compiler boundary. No body acceptance is presumed. -/
theorem compiler_body_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (initial : runtime.compiler.FunctionCompiler A)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (C : context)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial initial
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) (ctx.locals.val.map Translate.valueType)
      data env ctx (Wasm1.Loop.initialBlockType ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)))
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = ctx.locals.val.map Translate.valueType)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes (Wasm1.Loop.initialBlockType ctx.results.val) = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (ledger : ReachedCompilerLedger initial []) :
    code.validate_body_with_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx 0#u32 .Wasm1 initial ⦃ _ => True ⦄ := by
  let inv := fun (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) =>
    st.core.ctrls.val = [] ∨
      (IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial compiler
        (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
        (ctx.results.val.map Translate.valueType) (ctx.locals.val.map Translate.valueType)
        data env ctx (Wasm1.Loop.initialBlockType ctx.results.val) st.core ∧
       ReachedCompilerLedger compiler st.core.vals.val)
  have names := OrdinaryNamespaces.of_initial initialLocals localsMatch metadata signatures
  have steps : ReachedBody.StepTotalOn (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx 0#u32 .Wasm1 inv := by
    intro st before held nonempty inbounds next advance
    rcases held with closed | ⟨point,held⟩
    · exact False.elim (nonempty closed)
    obtain ⟨⟨reply,out,after⟩,run,observed⟩ := WP.spec_imp_exists
      (point.reader_total ops law names held bodyBound 0#u32 next advance inbounds data.val[st.core.pos.val])
    rw [run,WP.spec_ok]
    intro success
    change reply = .Ok () at success
    subst reply
    have raw := profile_wasm1_raw _ _ out data env ctx 0#u32 _ before after run
    obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
    let pending := state.boundary.pending next advance inbounds
    have forward := (pending.accepted_after _ before after out.core raw).2.1
    refine ⟨?_,forward⟩
    rcases point.advance_or_closed ops law C initialLocals localsMatch metadata matched contextLocals signatures
      bodyResults bodyBound next advance inbounds out.core raw with closed | fresh
    · exact Or.inl closed
    · exact Or.inr ⟨fresh,held.reader_wasm1 ops law pending out.core (observed rfl) raw⟩
  have initialization : code.initial_state env ctx 0#u32 .Wasm1 ⦃ result =>
      ∀ st, result = .Ok st → inv initial st ⦄ := by
    rw [code.initial_state,code.start_function.raw_spec]
    simp only [bind_ok,WP.spec_ok,core.result.Result.Ok.injEq]
    intro st same
    subst st
    simpa [alloc.vec.Vec.deref,inv] using (Or.inr ⟨point,ledger⟩ : inv initial ⟨Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)⟩)
  exact WP.spec_mono (code.validate_body_with_profile.total_on _ data env ctx 0#u32 .Wasm1 inv
    (fun _ => True) initial initialization steps (by intros; trivial)) (by simp)
end Exec.Code
