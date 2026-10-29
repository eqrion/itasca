import Itasca.Runtime.Compiler.Body.Reader.Control.SourceBranchInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.BranchCallbackExitSlots
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2

/-!
Structured compiler branch exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Source Branch Exit Slots -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Typed source label selection supplies every transfer and target premise
needed by the actual unconditional branch callback. -/
theorem StructuredCompilerPrefix.br_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (label : before.reachable = true → ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes raw = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_callback_exit_slots ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,selected,input⟩ := label live
  obtain ⟨index,frame,source,found,frameAt,shape,height,sourceAt,sourceWidth⟩ :=
    invariant.branch_layout live depth.val scope selected discarded input
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  apply compiler_branch_exit_slots ops law before middle index frame depth source 0#u32 found frameAt
    (by change source.val+(frameBranchWidth frame).val+0 = before.height.val; omega) order
    (by omega) held branch

/-- Conditional source label selection additionally bounds the consumed i32
selector and the local continuation around an actual transfer. -/
theorem StructuredCompilerPrefix.br_if_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (label : before.reachable = true → ∃ scope discarded stack,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes raw = stack++[.I32] ∧ stack = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_if_callback_exit_slots ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,stack,selected,input,targetStack⟩ := label live
  obtain ⟨index,frame,source,condition,found,frameAt,shape,height,sourceAt,sourceWidth,conditionAt,conditionSlot⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have room := invariant.codeBudget
  have resumeFits : before.function.code.val.length+3 < 2^32 := by
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  let resume : U32 := UScalar.ofNatCore (before.function.code.val.length+3) resumeFits
  exact compiler_branch_if_exit_slots ops law before middle index frame depth source condition resume
    found frameAt (by omega) conditionAt rfl order (by omega) held branch

end Itasca.Runtime.Code

end

/-! ## Reader Branch Exit Slots -/

section

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code

end
