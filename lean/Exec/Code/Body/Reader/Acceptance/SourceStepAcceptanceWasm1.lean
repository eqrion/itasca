import Exec.Code.Body.Reader.Source.SourceOpcodeExclusionWasm1
import Exec.Code.Body.Reader.Acceptance.SourceBoundScalarAcceptanceWasm1
import Exec.Code.Body.Reader.Acceptance.SourceBoundPointAcceptanceWasm1
import Exec.Code.Body.Reader.Control.SourceBoundControlAcceptanceWasm1
import Exec.Code.Body.Reader.Memory.SourceBoundStatefulMemoryAcceptanceWasm1
import Exec.Code.Body.Reader.Table.SourceBoundTableAcceptanceWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Complete Wasm 1 reached-step acceptance from independent validation and
source-derived resource bounds, including unreachable instructions and tables. -/
theorem IndexedTableReaderCompilerPointWasm1.step_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions
      (ctx.results.val.map Translate.valueType) localTypes data env ctx bodyBt st)
    (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (C : context) (matched : EnvTranslation.Matches env ctx C)
    (ledger : ReachedCompilerLedger compiler st.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env
      ctx index .Wasm1 data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index _ before after reference
  have progress := pending.accepted_after recorder before after out.core raw
  have forward : next.val ≤ out.core.pos.val := progress.2.1
  have liftOrdinary
      (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st with pos := next}} data env ctx index .Wasm1
        data.val[st.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => if counter = .instructions then 1 else 0) ⦄) :
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st with pos := next}} data env ctx index .Wasm1
        data.val[st.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => bodyResourceRate counter * (out.core.pos.val-st.pos.val)) ⦄ := by
    apply WP.spec_mono acceptance
    intro result held
    refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
    intro counter
    cases counter <;> simp [bodyResourceRate] <;> omega
  cases source_opcode_family data.val[st.pos.val] with
  | scalar kind byte =>
    apply liftOrdinary
    exact point.scalar_available_from_source ops bound allocation localsMatch before after final out room budget
      index nonempty next advance inbounds kind byte reference suffix
  | control kind byte =>
    exact point.control_available_from_source ops law bound allocation metadata signatures bodyResults ledger before after final out room budget
      index nonempty next advance inbounds kind byte reference suffix
  | table byte =>
    exact point.table_available_from_source ops law bound allocation ledger before after final out room budget
      index nonempty next advance inbounds (by simpa [global_simps] using byte) reference suffix
  | typedSelect byte =>
    exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after
      (by rw [byte]; simp) reference)
  | integer op base byte =>
    apply liftOrdinary
    exact point.numeric_available_from_source ops bound allocation before after final out room budget
      index nonempty next advance inbounds op base byte reference suffix
  | float op base byte =>
    apply liftOrdinary
    exact point.float_available_from_source ops bound allocation before after final out room budget
      index nonempty next advance inbounds op base byte reference suffix
  | sign op extension byte =>
    have bounded := integerOpcode_byte op
    have high : 192 ≤ data.val[st.pos.val].val := by rw [byte]; scalar_tac
    exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after
      (by tauto) reference)
  | load op byte =>
    apply liftOrdinary
    exact point.memory_load_available_from_source ops bound allocation before after final out room budget
      index nonempty next advance inbounds op byte reference suffix
  | store op byte =>
    apply liftOrdinary
    exact point.memory_store_available_from_source ops bound allocation before after final out room budget
      index nonempty next advance inbounds op byte reference suffix
  | stateful member =>
    by_cases supported : data.val[st.pos.val].val ∈ [63,64]
    · apply liftOrdinary
      exact point.stateful_memory_available_from_source ops bound allocation C matched ledger before after final out room budget
        index nonempty next advance inbounds _ supported rfl reference suffix
    · have absent : (37 ≤ data.val[st.pos.val].val ∧ data.val[st.pos.val].val ≤ 39) ∨
          192 ≤ data.val[st.pos.val].val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member supported
        omega
      exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after (by tauto) reference)
  | misc byte =>
    exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after
      (by rw [byte]; simp) reference)
  | simd byte =>
    exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after
      (by rw [byte]; simp) reference)
  | reserved rejected =>
    exact False.elim (source_opcode_rejected_wasm1 recorder _ out data env ctx index _ before after
      (by rcases rejected.absent with low | high <;> tauto) reference)

end Exec.Code
