import Exec.Code.Local.Relations.Common.StatefulLowering
import Exec.Code.Local.Callbacks.Calls.CompilerIndirectTactic
import Exec.Code.Body.Reader.Memory.StatefulMemoryReaderWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_stateful_single_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (single : statefulUsesPair op = false)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect = before.function.indirect := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulUsesPair] at single
    all_goals first | contradiction | skip
    all_goals simp only [statefulLowering] at accepted
    all_goals repeat' indirect_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_indirect ops law before after state (.Ok ()) accepted

theorem reader_memory_metadata_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (member : opcode.val ∈ [63,64])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨op,single,arguments,callback,post⟩ := reader_stateful_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out opcode member byte accepted
  rw [stateful_callback_lower ops before out op 0#u32 0#u32 arguments] at callback
  exact compiler_stateful_single_indirect ops law before after out op 0#u32 0#u32 single callback
end Exec.Code
