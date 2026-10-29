import Itasca.Runtime.Compiler.Body.Reader.Control.SourceControlCapacity
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedEnterAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedElseAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedEndAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedBranchAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedConditionalBranchAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedReturnAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source validation and conservative body bounds construct actual acceptance
for every metadata-producing control/call reader. The resource effect is paid
by consumed source bytes; no target-success or callback-demand premise occurs. -/
theorem IndexedTableReaderCompilerPointWasm2.control_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions
      (ft.results.val.map Translate.valueType) localTypes data env sourceLocals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨capacity,scope,coordinate,progress⟩ := point.control_capacity_from_source before after final out bound room
    budget nonempty next advance inbounds kind byte reference suffix
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have currentMetadata : FunctionParameterSlots compiler env := by
    simpa only [FunctionParameterSlots,state.compiled.metadata.fields.2.1] using metadata
  have currentSignatures : SignatureSequence compiler.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  rw [byte] at reference ⊢
  have liftEffect (allowance : ChargeCounter → Nat) (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter)
      (acceptance : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2 kind.opcode compiler
        ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2 kind.opcode compiler
        ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
    apply WP.spec_mono acceptance
    intro result held
    refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
    intro counter
    have span : 1 ≤ out.core.pos.val-st.core.pos.val := by omega
    exact (paid counter).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (bodyResourceRate counter) span)
  cases kind with
  | block =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_enter_available_wasm2 pending .block (by simp [Wasm2.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | loop =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_enter_available_wasm2 pending .loop (by simp [Wasm2.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | if_ =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_enter_available_wasm2 pending .then_ (by simp [Wasm2.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | else_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_else_available_wasm2 pending ops bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources (capacity.mono (by decide)) ledger.fixups byte reference
  | end_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_end_available_wasm2 ops bound allocation state.compiled recorder before after _ out data env
      ⟨sourceLocals,ft.results⟩ index (capacity.mono (by decide)) coordinate reference
  | br =>
    apply liftEffect (fun counter => if counter = .instructions then 2 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_br_available_wasm2 pending ops law bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
      (capacity.mono (by decide)) ledger.fixups byte reference
  | br_if =>
    apply liftEffect (fun counter => if counter = .instructions then 3 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_br_if_available_wasm2 pending ops law bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
      (capacity.mono (by decide)) ledger.fixups byte reference
  | return_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_return_available_wasm2 pending ops bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.reach.current (capacity.one (by decide)) reference
  | call =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_call_available_wasm2 pending ops bound allocation recorder before after compiler out
      ⟨sourceLocals,ft.results⟩ (capacity.one (by decide)) currentMetadata state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) byte reference
  | call_indirect =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_profile_indirect_call_available_wasm2 pending ops bound allocation recorder before after compiler out
      ⟨sourceLocals,ft.results⟩ (capacity.one (by decide)) currentSignatures state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) ledger.indirect byte reference

end Itasca.Runtime.Code
