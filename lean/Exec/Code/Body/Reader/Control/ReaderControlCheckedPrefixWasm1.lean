import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Body.Reader.Control.ControlReaderKind
import Exec.Code.Body.Reader.Control.ReaderEnterInstructionPrefixWasm1
import Exec.Code.Body.Reader.Control.ReaderEnterExitSlotsWasm1
import Exec.Code.Body.Reader.Control.ReaderElseInstructionPrefix
import Exec.Code.Body.Reader.Control.ReaderElseExitSlots
import Exec.Code.Body.Reader.Control.ReaderEndInstructionPrefix
import Exec.Code.Body.Reader.Control.ReaderEndExitSlots
import Exec.Code.Body.Reader.Control.ReaderRootInstructionPrefix
import Exec.Code.Body.Reader.Control.ReaderBranchInstructionPrefix
import Exec.Code.Body.Reader.Control.ReaderBranchExitSlots
import Exec.Code.Body.Reader.Control.ReaderTerminalInstructionPrefix
import Exec.Code.Body.Reader.Calls.ReaderCallCheckedPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- All control-reader forms preserve instruction and exit-slot checking at
an actual Wasm 1 source boundary. Root END additionally checks the completed
code before the final compiler publication check is called. -/
theorem StructuredReaderCompilerStateWithTablesWasm1.control_checked_prefix
    {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (C : context)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (metadata : FunctionParameterSlots before env) (signatures : SignatureSequence before.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (maps : ControlMapPublication before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.pos.val+1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (kind : ControlReaderKind)
    (byte : data.val[st.pos.val]'inbounds = kind.opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  let p := state.boundary.pending next advance inbounds
  have sourceBound := state.boundary.source_bound
  have positionBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  have coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := state.compiled.cursor
    omega
  cases kind with
  | block =>
    refine ⟨reader_enter_open_instructions_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach held code.OP_BLOCK (.inl rfl) ?_ ?_,
      reader_enter_exit_slots_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach exits code.OP_BLOCK (.inl rfl) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte
      | simpa only [ControlReaderKind.opcode,global_simps] using accepted
  | loop =>
    refine ⟨reader_enter_open_instructions_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach held code.OP_LOOP (.inr (.inl rfl)) ?_ ?_,
      reader_enter_exit_slots_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach exits code.OP_LOOP (.inr (.inl rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte
      | simpa only [ControlReaderKind.opcode,global_simps] using accepted
  | if_ =>
    refine ⟨reader_enter_open_instructions_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach held code.OP_IF (.inr (.inr rfl)) ?_ ?_,
      reader_enter_exit_slots_wasm1 p ops law initial before after out types functions _ locals parents current
        state.compiled state.reach exits code.OP_IF (.inr (.inr rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte
      | simpa only [ControlReaderKind.opcode,global_simps] using accepted
  | else_ =>
    exact ⟨reader_else_open_instructions_wasm1 p ops law initial before after out state.compiled state.sources held (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_else_exit_slots_wasm1 p ops law initial before after out state.compiled state.sources state.fronts state.reach.current exits (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | br =>
    exact ⟨reader_br_open_instructions_wasm1 p ops law initial before after out state.compiled state.sources state.fronts
        state.reach.current positionBound fixups coordinate held (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_exit_slots_wasm1 p ops law initial before after out state.compiled state.sources state.fronts
        state.reach.current exits (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | br_if =>
    exact ⟨reader_br_if_open_instructions_wasm1 p ops law initial before after out state.compiled state.sources state.fronts
        state.reach.current positionBound held (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_if_exit_slots_wasm1 p ops law initial before after out state.compiled state.sources state.fronts
        state.reach.current positionBound exits (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | return_ =>
    exact reader_return_open_instructions_wasm1 p ops law initial before after out state.compiled state.sources bodyResults
      state.reach.current sourceBound bodyBound held exits (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)
  | call =>
    exact reader_call_checked_prefix_wasm1 p ops law initial before after out state.compiled metadata
      state.reach.current sourceBound bodyBound held exits byte (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)
  | call_indirect =>
    exact reader_indirect_call_checked_prefix_wasm1 p ops law initial before after out state.compiled C matched contextLocals signatures
      state.reach.current sourceBound bodyBound held exits byte (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)
  | end_ =>
    by_cases root : savedCurrent.form = .body
    · obtain ⟨parentsEmpty,savedEmpty⟩ := state.root_scopes root
      subst parents savedParents
      obtain ⟨checked,empty⟩ := state.root_checked_instructions (ctx := ctx) ops law root bodyResults next advance inbounds out sourceBound
        bodyExtent initialLayout initialLocals initialCapacity maps held exits byte (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)
      constructor
      · intro index instruction found
        exact .checked (checked instruction (List.mem_of_getElem? found))
      · intro frame member
        rw [empty] at member
        simp at member
    · have nonRoot : current.form ≠ .body := by
        intro form
        have matching := state.sources.current.form
        rw [form] at matching
        have savedBody : savedCurrent.form = .body := by
          generalize savedEq : savedCurrent.form = actual at matching
          cases matching
          rfl
        exact root savedBody
      exact ⟨reader_nested_end_open_instructions_wasm1 p ops law initial before after out types functions _ locals parents current
          state.compiled nonRoot maps held bodyExtent (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
        reader_nested_end_exit_slots_wasm1 p ops law initial before after out types functions _ locals parents current
          state.compiled nonRoot maps exits bodyExtent (by simpa only [p,ReaderBoundaryWasm1.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩

end Exec.Code
