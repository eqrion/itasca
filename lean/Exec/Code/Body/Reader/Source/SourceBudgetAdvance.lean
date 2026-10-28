import Exec.Code.Body.Reader.Common.AcceptedReaderAdvance
import Exec.Code.Local.Capacity.BodyResourceRoom

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The reached certificate and all compiler counters are retained together.
The counters are paid by consumed source bytes, relative to function start. -/
def SourceBudgetReachedBodyWasm2 {A} (initial : runtime.compiler.FunctionCompiler A)
    (C : context) (locals : List valtype) (data : Slice U8) (env : module.Env)
    (sourceLocals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.BodyState) : Prop :=
  ReachedBodyWasm2 initial C locals data env sourceLocals index ft compiler st ∧
    SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val

/-- A source-paid accepted step preserves both executable evidence and the
budget used to construct capacity for the next step. One opcode byte pays
ordinary and structured callbacks; table readers use their longer span. -/
theorem source_budget_reader_advance_wasm2 {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
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
        CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        SourceBudgetReachedBodyWasm2 initial C locals data env sourceLocals index ft result.2.2 out ∧
        next.val ≤ out.core.pos.val ⦄ := by
  apply WP.spec_mono (accepted_reader_advance_wasm2 ops law initial compiler C locals data env sourceLocals
    index ft st out point ledger layout localsMatch metadata matched contextLocals signatures bodyBound
    nonempty next advance inbounds allowance acceptance)
  intro result held
  refine ⟨held.1,held.2.1,⟨held.2.2.1,?_⟩,held.2.2.2.2⟩
  exact budget.advance held.2.2.2.1 (by have progress := held.2.2.2.2; omega) paid

end Itasca.Runtime.Code
