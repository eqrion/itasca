import Exec.Code.Body.Reader.Table.StructuredReaderCompilerRoot
import Exec.Code.Body.Reader.Control.StructuredRootInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual root END checks every stored instruction from its typed preceding stack and retained exits. -/
theorem StructuredReaderCompilerStateWasm2.root_checked_instructions {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals
      data env ctx.locals index ft st [] current [] savedCurrent)
    (root : savedCurrent.form = .body)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (exits : FrameExitSlotBounds before)
    (byte : data.val[st.core.pos.val]'inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0x0b#u8 before = .ok (.Ok (), out, after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm2_spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Wasm2.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Wasm2.outputs, Wasm2.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Sequence.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Wasm2.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translate.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = ft.results.val.map Translate.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Sequence.Realizes false savedCurrent.vals (savedCurrent.outs.map Translate.valueType) := by
      simpa [p, ReaderBoundaryWasm2.pending, mono] using realizes
    have decoded := realized_concrete_types concrete actual
    simpa [rawEq, outs] using decoded.symm
  have consumed : st.core.pos.val < out.core.pos.val := encoded.span.1
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    rw [bodyExtent]
    exact Nat.add_le_add_left bounded _
  have entry := state.compiled.entryChain.root_entered rfl
  exact structured_root_checked_instructions ops law state.compiled sourceForm entry front results
    initialLayout initialLocals initialCapacity ((Nat.le_of_lt inbounds).trans sourceBound)
    out.core savedCurrent.ctrl.kind savedCurrent.bt stack exits maps held consumed endBound callback

end Itasca.Runtime.Code
