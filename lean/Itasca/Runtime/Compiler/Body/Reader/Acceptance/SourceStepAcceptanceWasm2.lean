import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeFamilies
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceMiscPrefix
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundScalarAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundPointAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundNumericExtensionAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundStatefulAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.SourceBoundControlAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSourceBoundAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Simd.SourceBoundSimdAcceptance
import Itasca.Visitor.ReaderAcceptedProgress

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Complete Wasm 2 reached-step acceptance from independent source validation
and source-derived resource bounds. Every opcode family, including dead code,
SIMD, branches, and streamed tables, is covered. No target-success, accepted
target trace, or completed caller-supplied code certificate is assumed. -/
theorem IndexedTableReaderCompilerPointWasm2.step_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions
      (ft.results.val.map Translate.valueType) localTypes data env sourceLocals index ft st)
    (localsMatch : initial.function.locals = sourceLocals)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (C : context) (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have progress := code.step_profile.accepted_progress recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2
    st out before after state.boundary.bounds.size state.boundary.opened.shape.core (by simp)
    state.boundary.bounds.ctrls nonempty inbounds next advance reference
  have liftOrdinary
      (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
        data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => if counter = .instructions then 1 else 0) ⦄) :
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
        data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
    apply WP.spec_mono acceptance
    intro result held
    refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
    intro counter
    cases counter <;> simp [bodyResourceRate] <;> omega
  cases source_opcode_family data.val[st.core.pos.val] with
  | scalar kind byte =>
    apply liftOrdinary
    exact point.scalar_available_from_source ops bound allocation localsMatch before after final out room budget
      nonempty next advance inbounds kind byte reference suffix
  | control kind byte =>
    exact point.control_available_from_source ops law bound allocation metadata signatures ledger before after final out room budget
      nonempty next advance inbounds kind byte reference suffix
  | table byte =>
    exact point.table_available_from_source ops law bound allocation ledger before after final out room budget
      nonempty next advance inbounds byte reference suffix
  | typedSelect byte =>
    apply liftOrdinary
    exact point.typed_select_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds byte reference suffix
  | integer op base byte =>
    apply liftOrdinary
    exact point.numeric_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds op base byte reference suffix
  | float op base byte =>
    apply liftOrdinary
    exact point.float_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds op base byte reference suffix
  | sign op extension byte =>
    apply liftOrdinary
    exact point.sign_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds op extension byte reference suffix
  | load op byte =>
    apply liftOrdinary
    exact point.memory_load_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds op byte reference suffix
  | store op byte =>
    apply liftOrdinary
    exact point.memory_store_available_from_source ops bound allocation before after final out room budget
      nonempty next advance inbounds op byte reference suffix
  | stateful member =>
    apply liftOrdinary
    exact point.stateful_base_available_from_source ops bound allocation C matched ledger before after final out room budget
      nonempty next advance inbounds _ member rfl reference suffix
  | misc byte =>
    have canonical := reference
    rw [byte] at canonical
    obtain ⟨sub,prefixEnd,decoded,accepted⟩ := source_misc_prefix recorder _ out data env ⟨sourceLocals,ft.results⟩ index
      before after canonical
    apply liftOrdinary
    rcases accepted with small | bulk
    · obtain ⟨op,extension,subEq⟩ := source_saturating_descriptor sub small
      exact point.saturating_available_from_source ops bound allocation before after final out room budget
        nonempty next advance inbounds op extension sub prefixEnd subEq decoded byte reference suffix
    · exact point.stateful_bulk_available_from_source ops bound allocation C matched ledger before after final out room budget
        nonempty next advance inbounds sub prefixEnd bulk decoded byte reference suffix
  | simd byte =>
    apply liftOrdinary
    exact point.simd_available_from_source ops bound allocation C matched ledger before after final out room budget
      nonempty next advance inbounds byte reference suffix
  | reserved rejected =>
    exact False.elim (rejected.rejects recorder _ out data env ⟨sourceLocals,ft.results⟩ index _ before after reference)

end Itasca.Runtime.Code
