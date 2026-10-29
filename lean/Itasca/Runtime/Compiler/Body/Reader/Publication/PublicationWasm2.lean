import Itasca.Runtime.Compiler.Body.Reader.Replay.CallbackProfile
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterPublicationWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.EndPublication
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTablePublication
import Itasca.Visitor.ReaderAcceptedProgress
import Itasca.Wasm2.Trace.TableBytes

/-!
Every accepted Wasm 2 reader step preserves both publication invariants from its source-typed reached prefix, including unreachable code and every complete-profile callback family.

Main declarations: `reader_publication_wasm2`. A direct consumer is `Compiler.Body.Reader.Publication.SourcePublicationAdvanceWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Every accepted Wasm 2 reader step preserves both publication invariants
from its source-typed reached prefix, including unreachable code and every
complete-profile callback family. -/
theorem reader_publication_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env .Wasm2 localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases h2 : opcode = 2#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after) := by simpa only [← h2] using accepted
    exact reader_enter_publication_wasm2 p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .block (.inl rfl) h2 call
  by_cases h3 : opcode = 3#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after) := by simpa only [← h3] using accepted
    exact reader_enter_publication_wasm2 p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .loop (.inr (.inl rfl)) h3 call
  by_cases h4 : opcode = 4#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after) := by simpa only [← h4] using accepted
    exact reader_enter_publication_wasm2 p ops law initial before after out ctx types functions returns locals parents current
      invariant reach signatures coordinates maps extent .then_ (.inr (.inr rfl)) h4 call
  by_cases h11 : opcode = 11#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after) := by simpa only [← h11] using accepted
    exact reader_end_publication_wasm2 p ops law initial before after out ctx types functions returns locals parents current
      invariant coordinates maps extent h11 call
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by
    have cursor := invariant.cursor
    have bounded := p.inbounds
    change p.start.val < data.length at bounded
    omega
  let sourceState : code.BodyState := {core := {st.core with pos := p.start}}
  have nonempty : sourceState.core.ctrls.val ≠ [] := by
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    change st.core.ctrls.val ≠ []
    rw [controls]
    simp
  have progress := code.step_profile.accepted_progress
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index .Wasm2 sourceState out before after
    p.size ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩ (by simp [sourceState]) p.ctrls nonempty p.inbounds st.core.pos p.pos accepted
  have forward : before.next_source.val ≤ out.core.pos.val := by
    have cursor := invariant.cursor
    have position := p.pos
    omega
  by_cases h14 : opcode = 14#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),out,after) := by simpa only [← h14] using accepted
    rw [CallbackTrace.dispatch_br_table] at call
    exact reader_table_publication_wasm2 ops law before after st out data env coordinates maps inside forward call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by
    simp only [global_simps]
    tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_callback_profile_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after blocked accepted
  exact compiler_non_scope_hook_publication ops law before after out.core
    (.of_range action range ordinary) coordinates maps inside forward callback

end Itasca.Runtime.Compiler
