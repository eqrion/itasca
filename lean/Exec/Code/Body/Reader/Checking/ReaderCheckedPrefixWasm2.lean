import Exec.Code.Body.Reader.Checking.ReaderNoncontrolCheckedPrefixWasm2
import Exec.Code.Body.Reader.Control.ReaderControlCheckedPrefixWasm2
import Exec.Code.Body.Reader.Table.ReaderTableInstructionPrefixWasm2
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint

namespace Exec.Code
open Aeneas Aeneas.Std Itasca


/-- Every accepted Wasm 2 reader step preserves both concrete checking
invariants from the retained source boundary. This covers the complete profile
and does not assume an accepted future callback trace or final certificate. -/
theorem IndexedTableReaderCompilerPointWasm2.checked_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (localsMatch : initial.function.locals = ctx.locals) (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyExtent : initial.function.body_end.val = initial.function.body_start.val+data.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (maps : ControlMapPublication before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have sourceBound := state.boundary.source_bound
  have beforeBound := state.compiled.metadata.body_bound bodyBound
  obtain ⟨sameSignatures,sameFunctions,_,_,sameLocals,_,_,sameStart,sameEnd,_⟩ := state.compiled.metadata.fields
  have beforeLocals : before.function.locals = ctx.locals := sameLocals.trans localsMatch
  have beforeMetadata : FunctionParameterSlots before env := by
    simpa only [FunctionParameterSlots,sameFunctions] using metadata
  have beforeSignatures : SignatureSequence before.signatures.val env.types.val := by
    simpa only [sameSignatures] using signatures
  have beforeExtent : before.function.body_end.val = before.function.body_start.val+data.length := by
    rw [sameEnd,sameStart]
    exact bodyExtent
  by_cases table : opcode = 14#u8
  · rw [table,Wasm2.CallbackTrace.dispatch_br_table] at accepted
    exact reader_table_open_instructions_wasm2 p ops law initial before after out state.compiled state.sources state.fronts
      state.reach.current sourceBound beforeBound point.tables fixups held exits accepted
  by_cases noncontrol : opcode.val ∉ [2,3,4,5,11,12,13,14,15,16,17]
  · exact reader_noncontrol_checked_prefix_wasm2 p ops law initial before after out ctx rfl C state.compiled beforeLocals matched
      contextLocals state.reach.current sourceBound beforeBound opcode noncontrol held exits
      (by simpa only [p,ReaderBoundaryWasm2.pending] using byte) accepted
  · have member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17] := by
      have noTable : opcode.val ≠ 14 := fun equal => table (UScalar.eq_of_val_eq equal)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at noncontrol ⊢
      tauto
    obtain ⟨kind,same⟩ := ControlReaderKind.of_opcode_mem opcode member
    rw [same] at byte accepted
    exact state.control_checked_prefix ops law ctx rfl C matched contextLocals beforeMetadata beforeSignatures
      initialLayout initialLocals initialCapacity beforeExtent beforeBound maps fixups held exits next advance inbounds out kind byte accepted

end Exec.Code
