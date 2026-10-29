import Itasca.Runtime.Compiler.Body.Reader.Replay.ReachedSafety
import Itasca.Runtime.Compiler.Body.Control.Closing.IndexedAdvanceOrClosed
import Itasca.Visitor.InvariantBodyLoop
import Itasca.Visitor.ReaderAcceptedProgress
import Itasca.Wasm2.Trace.Body

/-!
A rejected body needs no retained suffix; an accepted open boundary retains both the exact compiler/source point and its quantitative callback ledger.

Main declarations: `ReachedBodyWasm2`. A direct consumer is `Compiler.Module.CompileTotal`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A rejected body needs no retained suffix; an accepted open boundary retains
both the exact compiler/source point and its quantitative callback ledger. -/
def ReachedBodyWasm2 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : module.Env)
    (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  st.core.ctrls.val = [] ∨
    (IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft st ∧
      ReachedCompilerLedger compiler st.core.vals.val)

theorem compiler_body_steps_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max) :
    ReachedBody.StepTotalOn (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ⟨sourceLocals,ft.results⟩ index .Wasm2 (ReachedBodyWasm2 initial C locals data env sourceLocals index ft) := by
  intro st compiler held nonempty inbounds next advance
  rcases held with closed | ⟨point,ledger⟩
  · exact False.elim (nonempty closed)
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have namespaces : OrdinaryNamespaces initial env ⟨sourceLocals,ft.results⟩ :=
    .of_initial layout localsMatch metadata signatures
  obtain ⟨⟨reply,out,after⟩,run,observed⟩ := WP.spec_imp_exists
    (point.reader_total ops law namespaces signatures ledger bodyBound next advance inbounds data.val[st.core.pos.val])
  rw [run,WP.spec_ok]
  intro accepted
  dsimp only at accepted
  subst reply
  have fresh := ledger.reader_wasm2 ops law pending out ⟨sourceLocals,ft.results⟩ (observed rfl) (by simpa only [pending,ReaderBoundaryWasm2.pending] using run)
  have moved := point.advance_or_closed ops law C layout localsMatch metadata matched contextLocals signatures
    bodyBound next advance inbounds out run
  have cursor := code.step_profile.accepted_progress
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ⟨sourceLocals,ft.results⟩ index .Wasm2
    st out compiler after state.boundary.bounds.size state.boundary.opened.shape.core (by simp)
    state.boundary.bounds.ctrls nonempty inbounds next advance run
  refine ⟨?_,cursor⟩
  rcases moved with closed | point'
  · exact .inl closed
  · exact .inr ⟨point',fresh⟩

/-- Arbitrary remaining bytes return normally from the actual fresh compiler
state. Every callback premise is derived at its reached source boundary. -/
theorem compiler_body_wasm2_total {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial initial
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft (Wasm2.initial index))
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger initial [])
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max) :
    code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ⟨sourceLocals,ft.results⟩ index .Wasm2 initial ⦃ _ => True ⦄ := by
  apply WP.spec_mono (code.validate_body_with.total_on
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ⟨sourceLocals,ft.results⟩ index .Wasm2
    (ReachedBodyWasm2 initial C locals data env sourceLocals index ft) (fun _ => True) initial ?_
    (compiler_body_steps_wasm2 ops law initial C locals data env sourceLocals index ft layout localsMatch metadata
      matched contextLocals signatures bodyBound) (by intros; trivial))
  · intros; trivial
  · obtain ⟨result,run,held⟩ := WP.spec_imp_exists (code.initial_state.start env index)
    rw [run,WP.spec_ok]
    intro st accepted
    subst result
    obtain ⟨rfl,_⟩ := held
    exact .inr ⟨point,ledger⟩
end Itasca.Runtime.Compiler
