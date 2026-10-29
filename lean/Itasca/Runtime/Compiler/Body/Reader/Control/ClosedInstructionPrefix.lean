import Itasca.Runtime.Compiler.Body.Reader.Replay.CompilerBounds
import Itasca.Runtime.Compiler.Body.Reader.Control.RootInstructionPrefix

/-!
Closing the actual reader control stack publishes checks for every stored instruction.

Main declarations: `StructuredReaderCompilerStateWasm2.closed_checked_instructions`. A direct consumer is `Compiler.Body.Reader.Checking.SourceCheckedStepsWasm2`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Closing the actual reader control stack publishes checks for every stored instruction. -/
theorem StructuredReaderCompilerStateWasm2.closed_checked_instructions
    {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (closed : out.core.ctrls.val = [])
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    CheckedInstructionPrefix after.function := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback,read,encoded,realizes,zipper,afterState⟩ := reader_end_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have root : p.current.form = .body := by
    rcases zipper with ⟨root,empty,_⟩ | ⟨grandparents,parent,instruction,split,finished,opened⟩
    · exact root
    · obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := opened
      rw [controls] at closed
      simp at closed
  have root : savedCurrent.form = .body := by
    simpa only [p,ReaderBoundaryWasm2.pending] using root
  obtain ⟨parentsEmpty,savedEmpty⟩ := state.root_scopes root
  subst parents savedParents
  exact (state.root_checked_instructions (ctx := ctx) ops law root next advance inbounds out state.boundary.source_bound
    bodyExtent initialLayout initialLocals initialCapacity maps held exits byte accepted).1

end Itasca.Runtime.Code
