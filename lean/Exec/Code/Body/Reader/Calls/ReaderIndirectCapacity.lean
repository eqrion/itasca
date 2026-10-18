import Exec.Code.Body.Reader.Calls.ReaderIndirectCall
import Exec.Code.Body.Reader.Calls.ReaderIndirectCallWasm1
import Exec.Code.Local.Relations.Calls.IndirectCallMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source stack capacity follows the actual accepted indirect-call callback,
without requiring a retained source zipper or successful allocation premise. -/
theorem reader_indirect_call_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_call_indirect] at accepted
  obtain ⟨⟨index,table⟩,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_indirect_call_capacity ops law before after out.core index table callback

theorem reader_indirect_call_capacity_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL_INDIRECT before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  rw [VisitorTrace.dispatch_call_indirect] at accepted
  obtain ⟨index,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_indirect_call_capacity ops law before after out index 0#u32 callback
end Exec.Code
