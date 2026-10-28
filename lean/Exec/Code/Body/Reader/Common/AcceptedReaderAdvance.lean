import Exec.Code.Body.Relations.Common.ReachedBodySafetyWasm2
import Exec.Code.Local.Capacity.BudgetEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Reuse the complete accepted-step certificate after acceptance has been
constructed from source demand. This retains the executable prefix and all
auxiliary ledgers, together with the independently proved resource effect. -/
theorem accepted_reader_advance_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial compiler : runtime.compiler.FunctionCompiler A) (C : context) (locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (st out : code.BodyState)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial compiler
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (layout : LocalLayout initial) (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS=locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val+data.length≤Usize.max)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (allowance : ChargeCounter → Nat)
    (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        ReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2.2 out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ∧ next.val ≤ out.core.pos.val ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have namespaces : OrdinaryNamespaces initial env ⟨sourceLocals,ft.results⟩ :=
    .of_initial layout localsMatch metadata signatures
  obtain ⟨⟨reply,targetOut,after⟩,called,accepted,same,effect⟩ := WP.spec_imp_exists acceptance
  dsimp only at accepted same effect
  subst reply targetOut
  have normal := point.reader_total ops law namespaces signatures ledger bodyBound next advance inbounds
    data.val[st.core.pos.val]
  rw [called,WP.spec_ok] at normal
  have observed := normal rfl
  have fresh := ledger.reader_wasm2 ops law pending out ⟨sourceLocals,ft.results⟩ observed
    (by simpa only [pending,ReaderBoundaryWasm2.pending] using called)
  have moved := point.advance_or_closed ops law C layout localsMatch metadata matched contextLocals signatures
    bodyBound next advance inbounds out called
  have cursor := code.step_profile.accepted_progress
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ⟨sourceLocals,ft.results⟩ index .Wasm2
    st out compiler after state.boundary.bounds.size state.boundary.opened.shape.core (by simp)
    state.boundary.bounds.ctrls nonempty inbounds next advance called
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,after),called,rfl,rfl,?_,effect,cursor⟩
  rcases moved with closed | point'
  · exact .inl closed
  · exact .inr ⟨point',fresh⟩

end Itasca.Runtime.Code
