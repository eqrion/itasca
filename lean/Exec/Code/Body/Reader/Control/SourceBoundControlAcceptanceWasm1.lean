import Exec.Code.Body.Reader.Control.ControlReaderKindWasm1
import Exec.Code.Body.Reader.Source.SourceReaderCapacityWasm1
import Exec.Code.Body.Reader.Control.ReachedEnterAcceptanceWasm1
import Exec.Code.Body.Reader.Control.ReachedElseAcceptance
import Exec.Code.Body.Reader.Control.ReachedEndAcceptance
import Exec.Code.Body.Reader.Control.ReachedBranchAcceptanceWasm1
import Exec.Code.Body.Reader.Control.ReachedConditionalBranchAcceptanceWasm1
import Exec.Code.Body.Reader.Control.ReachedReturnAcceptance
import Exec.Code.Body.Reader.Calls.ReachedCallAcceptance
import Exec.Code.Body.Reader.Calls.ReachedIndirectCallAcceptance
import Exec.Code.Body.Relations.Common.ReachedCompilerLedger

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Every Wasm 1 control/call reader accepts with source-derived resource
bounds and retained source scope/layout evidence. -/
theorem IndexedTableReaderCompilerPointWasm1.control_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions
      (ctx.results.val.map Translate.valueType) localTypes data env ctx bodyBt st)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (ledger : ReachedCompilerLedger compiler st.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.pos.val] = kind.opcode)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => bodyResourceRate counter*(out.core.pos.val-st.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨capacity,scope,coordinate,progress⟩ := point.capacity_from_source_read before after final out bound room budget
    index nonempty next advance inbounds kind.opcode (kind.readWasm1 {st with pos := next} data env ctx) kind.actionWasm1
    (kind.dispatch_wasm1 recorder _ data env ctx before) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index kind.opcode before after canonical
  have currentMetadata : FunctionParameterSlots compiler env := by
    simpa only [FunctionParameterSlots,state.compiled.metadata.fields.2.1] using metadata
  have currentSignatures : SignatureSequence compiler.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx
    index kind.opcode compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => bodyResourceRate counter*(out.core.pos.val-st.pos.val)))
  have liftEffect (allowance : ChargeCounter → Nat) (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter)
      (acceptance : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) {st with pos := next} data env ctx
        kind.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out.core ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
      code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) {st with pos := next} data env ctx
        kind.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out.core ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => bodyResourceRate counter*(out.core.pos.val-st.pos.val)) ⦄ := by
    apply WP.spec_mono acceptance
    intro result held
    refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
    intro counter
    have span : 1 ≤ out.core.pos.val-st.pos.val := by omega
    exact (paid counter).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (bodyResourceRate counter) span)
  cases kind with
  | block =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_block_available_wasm1 pending ops bound allocation initial compiler recorder before after out.core
      state.compiled state.reach.current (capacity.one (by decide)) scope (by have pc := capacity.pc; omega)
      (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte)
      (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | loop =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_loop_available_wasm1 pending ops bound allocation initial compiler recorder before after out.core
      state.compiled state.reach.current (capacity.one (by decide)) scope (by have pc := capacity.pc; omega)
      (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte)
      (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | if_ =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_if_available_wasm1 pending ops bound allocation initial compiler recorder before after out.core
      state.compiled state.reach.current (capacity.one (by decide)) scope (by have pc := capacity.pc; omega)
      (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte)
      (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | else_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_else_available_wasm1 pending ops bound allocation initial compiler recorder before after out.core
      state.compiled state.sources (capacity.mono (by decide)) ledger.fixups (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | end_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_end_available_wasm1 ops bound allocation state.compiled recorder before after _ out.core
      data env ctx (capacity.mono (by decide)) coordinate (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | br =>
    apply liftEffect (fun counter => if counter = .instructions then 2 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_br_available_wasm1 pending ops law bound allocation initial compiler recorder before after out.core
      state.compiled state.sources state.fronts state.reach.current (capacity.mono (by decide)) ledger.fixups (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | br_if =>
    apply liftEffect (fun counter => if counter = .instructions then 3 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_br_if_available_wasm1 pending ops law bound allocation initial compiler recorder before after out.core
      state.compiled state.sources state.fronts state.reach.current (capacity.mono (by decide)) ledger.fixups (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | return_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_return_available_wasm1 pending ops bound allocation initial compiler recorder before after out.core
      state.compiled state.sources bodyResults state.reach.current (capacity.one (by decide)) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | call =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_call_available_wasm1 pending ops bound allocation recorder before after compiler out.core
      (capacity.one (by decide)) currentMetadata state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)
  | call_indirect =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    simpa only [ControlReaderKind.opcode,global_simps] using reached_reader_indirect_call_available_wasm1 pending ops bound allocation recorder before after compiler out.core
      (capacity.one (by decide)) currentSignatures state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) ledger.indirect (by simpa only [ControlReaderKind.opcode,global_simps,pending,ReaderBoundaryWasm1.pending] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using raw)

end Exec.Code
