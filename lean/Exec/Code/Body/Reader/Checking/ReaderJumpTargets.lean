import Exec.Code.Body.Reader.Checking.ReaderTargetBounds
import Exec.Code.Body.Reader.Checking.NonScopeTargetBounds
import Exec.Code.Body.Reader.Replay.SingleCallbackProfileWasm2
import Exec.Code.Body.Reader.Replay.SingleCallbackWasm1
import Itasca.Wasm2.Trace.TableBytes

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2

/-- Every accepted Wasm 1 step retains jump targets; no additional code-prefix,
stack-layout, or completed publication certificate premise is needed. -/
theorem reader_jump_targets_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (held : JumpTableBounds before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases opening : opcode = code.OP_BLOCK ∨ opcode = code.OP_LOOP ∨ opcode = code.OP_IF
  · exact reader_enter_target_bounds_wasm1 p ops law before after out held opcode opening rfl accepted
  by_cases ending : opcode = code.OP_END
  · have call : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx code.OP_END before = .ok (.Ok (),out,after) := by simpa only [← ending] using accepted
    exact reader_end_target_bounds_wasm1 p ops law before after out held ending call
  by_cases table : opcode = code.OP_BR_TABLE
  · have call : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),out,after) := by simpa only [← table] using accepted
    exact reader_table_target_bounds_wasm1 ops law before after st out data env ctx held call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_callback_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx opcode before after out blocked accepted
  exact compiler_non_scope_hook_target_bounds ops law before after out (.of_range action range ordinary) held callback

/-- Every accepted complete-profile Wasm 2 reader step retains bounded jump
targets, including SIMD, dead bodies, branches, references and streamed tables. -/
theorem reader_jump_targets_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases h2 : opcode = 2#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after) := by simpa only [← h2] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .block (.inl rfl) h2 call
  by_cases h3 : opcode = 3#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after) := by simpa only [← h3] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .loop (.inr (.inl rfl)) h3 call
  by_cases h4 : opcode = 4#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after) := by simpa only [← h4] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .then_ (.inr (.inr rfl)) h4 call
  by_cases h11 : opcode = 11#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after) := by simpa only [← h11] using accepted
    exact reader_end_target_bounds_wasm2 p ops law before after out ctx held h11 call
  by_cases h14 : opcode = 14#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),out,after) := by simpa only [← h14] using accepted
    rw [CallbackTrace.dispatch_br_table] at call
    exact reader_table_target_bounds_wasm2 ops law before after st out data env held call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by
    simp only [global_simps]
    tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_callback_profile_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after blocked accepted
  exact compiler_non_scope_hook_target_bounds ops law before after out.core (.of_range action range ordinary) held callback

end Exec.Code
