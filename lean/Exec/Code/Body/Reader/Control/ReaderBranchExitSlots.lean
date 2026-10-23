import Exec.Code.Body.Reader.Control.SourceBranchExitSlots
import Exec.Code.Body.Reader.Control.ReaderBranchIfLayout
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed br reading preserves the slot regions of recorded forward exits. -/
theorem reader_br_exit_slots_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_BR before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨depth,view,callback,read,post⟩ := reader_br_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_exit_slots ops law out.core depth view ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input⟩ := reader_br_layout_wasm2 p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,selected,input⟩

/-- Actual source-typed br_if reading preserves the slot regions of recorded forward exits. -/
theorem reader_br_if_exit_slots_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_BR_IF before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨depth,view,values,callback,read,post⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_if_exit_slots ops law out.core depth view sourceBound ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input,targetStack,concrete⟩ := reader_br_if_layout_wasm2 p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,_,selected,input,targetStack⟩

end Exec.Code
