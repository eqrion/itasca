import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedReferenceDemand
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ProfileAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.BodyReplay

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Common source-demand adapter for ordinary base instructions. Independent
reference validation supplies capacity and event sizes; the local reader proof
then establishes actual target acceptance. No target-success equation is an
input. -/
theorem source_bound_base_available_wasm2 {A R : Type}
    (ops : runtime.platform.Alloc A)
    {initial compiler : runtime.compiler.FunctionCompiler A} {data env ctx index st}
    (out : code.BodyState) (before after final : List Observation) (bound : Nat)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (metadata : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler st.core.pos.val)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (opcode : U8) (byte : data.val[st.core.pos.val] = opcode)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (plain : opcode.val ∉ [28,37,38,208,209,210,252,253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none) (misc : opcode ≠ code.OP_MISC_PREFIX)
    (read : Result (core.result.Result R error.OpError × code.OpIterState)) (action : R → Action)
    (description : code.step recorder {st.core with pos := next} data env ctx opcode before =
      CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before)
    (allowance : ChargeCounter → Nat)
    (readerAccepts : st.core.vals.val.length < Usize.max →
      code.step recorder {st.core with pos := next} data env ctx opcode before = .ok (.Ok (),out.core,after) →
      CallbackDemand compiler out.core bound →
      code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {st.core with pos := next} data env ctx opcode compiler ⦃ result => result.1 = .Ok () ∧
          result.2.1 = out.core ∧ CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm2 before st = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 data.val[st.core.pos.val] compiler ⦃ result =>
        result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄ := by
  have tail := code.body_loop_loop.accepted_tail recorder data env ctx index .Wasm2 st out before after final nonempty
    inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 recorder _ out data env ctx ctx index opcode before after
    ordinary plain sign misc rfl canonical
  have recorded := raw
  rw [description] at recorded
  have demand := reference_reader_demand final room budget metadata codeBudget sources cursor inbounds read action
    before after out recorded data env ctx index .Wasm2 tail
  rw [byte]
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    _ out.core data env ctx ctx index opcode compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget allowance) capacity ordinary plain sign misc rfl
    (readerAccepts capacity raw demand)

end Itasca.Runtime.Code
