import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndElseCompilation
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Checking.InstructionBounds
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects ControlInstructionPrefixes, RootMapPublication.
Each section documents its contracts and consumers.
-/

/-! ## ControlInstructionPrefixes -/

section

open Itasca.Representation

/-!
# Reader control instruction prefixes

Branch/table, else, scope entry and close readers retain instruction-prefix and exit-slot
certificates. Root-map publication composes the source and compiler control bounds.
-/

/-! ## SourceBranchInstructionPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A source loop frame points to its retained entry hook. -/
theorem FrameScope.loop_instruction_target {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {locals scope frame} (shape : FrameScope locals compiler scope frame) (loop : frame.kind = .Loop) :
    frame.start_pc.val ≤ compiler.function.code.length := by
  have kind := shape.kind
  have start := shape.start
  have entry := shape.entryBound
  cases form : scope.form <;> simp_all [ScopeForm.kind,SourceScope.frameStart]

/-- Typed source label selection supplies every transfer and target premise
needed by the actual unconditional branch callback. -/
theorem StructuredCompilerPrefix.br_open_instructions
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (label : before.reachable = true → ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Body.Stack.stackTypes raw = scope.front++discarded++scope.branchTypes)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_callback_open_instructions ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,selected,input⟩ := label live
  obtain ⟨index,frame,source,found,frameAt,shape,height,sourceAt,sourceWidth⟩ :=
    invariant.branch_layout live depth.val scope selected discarded input
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have room := invariant.codeBudget
  have codeFits : before.function.code.val.length+2 ≤ Usize.max := by
    have bound := invariant.codeBudget.code_capacity sourceBound
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  have offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max := by
    rw [invariant.sources]
    exact codeFits
  by_cases loop : frame.kind = .Loop
  · have width' : frame.params.val = slots scope.branchTypes := by simpa [frameBranchWidth,loop] using width
    exact compiler_branch_loop_open_instructions ops law before middle frame index depth source 0#u32
      found frameAt loop (by change source.val+frame.params.val+0 = before.height.val; omega)
      order (by omega) (shape.loop_instruction_target loop) codeFits offsetsFit coordinate held branch
  · have width' : frame.results.val = slots scope.branchTypes := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    exact compiler_branch_forward_open_instructions ops law before middle frame index depth source 0#u32
      found frameAt loop (by change source.val+frame.results.val+0 = before.height.val; omega)
      order (by omega) (fixups.lookup found (by omega)) codeFits offsetsFit coordinate held branch

/-- Conditional source label selection additionally bounds the consumed i32
selector and the local continuation around an actual transfer. -/
theorem StructuredCompilerPrefix.br_if_open_instructions
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (state : code.OpIterState) (depth : U32) (view : signature.ResultType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (label : before.reachable = true → ∃ scope discarded stack,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Body.Stack.stackTypes raw = stack++[.I32] ∧ stack = scope.front++discarded++scope.branchTypes)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_if_callback_open_instructions ops law before after state depth view held _ called
  intro live middle branch
  obtain ⟨scope,discarded,stack,selected,input,targetStack⟩ := label live
  obtain ⟨index,frame,source,condition,found,frameAt,shape,height,sourceAt,sourceWidth,conditionAt,conditionSlot⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by rw [slots_append]; omega
  have order : frame.height.val ≤ source.val := by omega
  have capacity := (invariant.live live).2.layout.capacity live
  have layout := (invariant.live live).2.layout.height
  have localsEq := (invariant.live live).2.localsEq
  rw [input] at layout
  simp only [slots_append,slots,show Itasca.Representation.width (.I32 : valtype) = 1 from rfl,localsEq] at layout
  have test : condition.val+1 ≤ before.function.slot_count.val := by omega
  have room := invariant.codeBudget
  have resumeFits : before.function.code.val.length+3 < 2^32 := by
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac
  let resume : U32 := UScalar.ofNatCore (before.function.code.val.length+3) resumeFits
  by_cases loop : frame.kind = .Loop
  · have width' : frame.params.val = slots scope.branchTypes := by simpa [frameBranchWidth,loop] using width
    exact compiler_branch_if_loop_open_instructions ops law before middle frame index depth source condition resume
      found frameAt loop (by omega) conditionAt rfl order (by omega) test
      (shape.loop_instruction_target loop) held branch
  · have width' : frame.results.val = slots scope.branchTypes := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    exact compiler_branch_if_forward_open_instructions ops law before middle frame index depth source condition resume
      found frameAt loop (by omega) conditionAt rfl order (by omega) test held branch

end Itasca.Compiler

end

/-! ## BranchExitSlots -/

section

/-!
Structured compiler branch exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Source Branch Exit Slots -/

section

namespace Itasca.Compiler
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
      Body.Stack.stackTypes raw = scope.front++discarded++scope.branchTypes)
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
      Body.Stack.stackTypes raw = stack++[.I32] ∧ stack = scope.front++discarded++scope.branchTypes)
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

end Itasca.Compiler

end

/-! ## Reader Branch Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed br reading preserves the slot regions of recorded forward exits. -/
theorem reader_br_exit_slots {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BR before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨depth,view,callback,read,post⟩ := reader_br p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_exit_slots ops law out.core depth view ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input⟩ := reader_br_layout p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,selected,input⟩

/-- Actual source-typed br_if reading preserves the slot regions of recorded forward exits. -/
theorem reader_br_if_exit_slots {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BR_IF before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨depth,view,values,callback,read,post⟩ := reader_br_if p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_if_exit_slots ops law out.core depth view sourceBound ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input,targetStack,concrete⟩ := reader_br_if_layout p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,_,selected,input,targetStack⟩

end Itasca.Compiler

end

end

/-! ## BranchInstructionPrefix -/

section

/-!
Actual source-typed br reading preserves checks of every stored word.

Main declarations: `reader_br_open_instructions` and `reader_br_if_open_instructions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed br reading preserves checks of every stored word. -/
theorem reader_br_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BR before = .ok (.Ok (),out,after)) : CompilerInstructionPrefix after := by
  obtain ⟨depth,view,callback,read,post⟩ := reader_br p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_open_instructions ops law out.core depth view sourceBound fixups coordinate ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input⟩ := reader_br_layout p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,selected,input⟩

/-- Actual source-typed br_if reading preserves checks of every stored word. -/
theorem reader_br_if_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val)
    (held : CompilerInstructionPrefix before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_BR_IF before = .ok (.Ok (),out,after)) : CompilerInstructionPrefix after := by
  obtain ⟨depth,view,values,callback,read,post⟩ := reader_br_if p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  apply invariant.br_if_open_instructions ops law out.core depth view sourceBound ?label held callback
  intro live
  obtain ⟨scope,discarded,selected,input,targetStack,concrete⟩ := reader_br_if_layout p same fronts
    (invariant.known live) (monomorphic live) depth view out read
  exact ⟨scope,discarded,_,selected,input,targetStack⟩

end Itasca.Compiler

end

/-! ## ElseExitSlots -/

section

/-!
Structured compiler else exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Else Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source THEN geometry provides the owned guard needed by actual ELSE in
live, terminated, and unentered arms. -/
theorem StructuredCompilerPrefix.else_exit_slots {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {jumpTables emit initial compiler after types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (sourceBt : blocktype) (condition : U32)
    (form : current.form = .then_ sourceBt condition) (bt : signature.BlockType)
    (normalStack : compiler.reachable = true → Body.Stack.stackTypes raw = current.front++current.results)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (held : FrameExitSlotBounds compiler)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have liveGuard : compiler.reachable = true → frame.if_pc ≠ none := by
    intro live absent
    have entered := (invariant.live live).1
    have guard := shape.guard
    simp [absent,form,SourceScope.guardPosition,entered] at guard
  have owned : ∀ guard, frame.if_pc = some guard → ∃ operand,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero operand core.num.U32.MAX) := by
    intro guard selected
    have same := shape.guard
    simp only [selected,Option.map_some,form,SourceScope.guardPosition] at same
    cases entered : current.entered with
    | false => simp [entered] at same
    | true =>
      have position : guard.val = current.entry := by simpa [entered] using same
      refine ⟨condition,?_⟩
      rw [position]
      have entry : current.entered = true → compiler.function.code.val[current.entry]? =
          some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode,form] using shape.entryCode
      exact entry entered
  apply compiler_else_exit_slots ops law compiler after state bt frame prior frames owned ?_ ?_ ?_ held called
  · intro absent
    by_cases live : compiler.reachable = true
    · exact False.elim (liveGuard live absent)
    · cases reachable : compiler.reachable <;> simp_all
  · intro live
    obtain ⟨entered,retained⟩ := invariant.live live
    have region := retained.layout.live_slots_fit live
    have height := shape.height entered
    have width := shape.results
    rw [normalStack live,retained.localsEq,slots_append] at region
    omega
  · have room := invariant.codeBudget
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac

end Itasca.Compiler

end

/-! ## Reader Else Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_exit_slots {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 5#u8 before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨callback,read,sourceForm,encoded,results,opened,afterState⟩ := reader_else p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Body.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have frontEq : current.front = Body.Stack.stackTypes outer := by
    rw [spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Body.Stack.stackTypes st.core.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ invariant.known live)).2
    have mono := monomorphic live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Body.Stack.stackTypes, List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_exit_slots ops law out.core _ condition form p.current.bt stack sourceBound held callback

end Itasca.Compiler

end

end

/-! ## ElseInstructionPrefix -/

section

/-!
Structured compiler else checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Else Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source THEN geometry provides the owned guard needed by actual ELSE in
live, terminated, and unentered arms. -/
theorem StructuredCompilerPrefix.else_open_instructions {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {jumpTables emit initial compiler after types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (sourceBt : blocktype) (condition : U32)
    (form : current.form = .then_ sourceBt condition) (bt : signature.BlockType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (held : CompilerInstructionPrefix compiler)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have liveGuard : compiler.reachable = true → frame.if_pc ≠ none := by
    intro live absent
    have entered := (invariant.live live).1
    have guard := shape.guard
    simp [absent,form,SourceScope.guardPosition,entered] at guard
  have owned : ∀ guard, frame.if_pc = some guard → ∃ operand,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero operand core.num.U32.MAX) := by
    intro guard selected
    have same := shape.guard
    simp only [selected,Option.map_some,form,SourceScope.guardPosition] at same
    cases entered : current.entered with
    | false => simp [entered] at same
    | true =>
      have position : guard.val = current.entry := by simpa [entered] using same
      refine ⟨condition,?_⟩
      rw [position]
      have entry : current.entered = true → compiler.function.code.val[current.entry]? =
          some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode,form] using shape.entryCode
      exact entry entered
  apply compiler_else_open_instructions ops law compiler after state bt frame prior frames owned ?_ ?_ held called
  · intro absent
    by_cases live : compiler.reachable = true
    · exact False.elim (liveGuard live absent)
    · cases reachable : compiler.reachable <;> simp_all
  · have room := invariant.codeBudget
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac

end Itasca.Compiler

end

/-! ## Reader Else Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (held : CompilerInstructionPrefix before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 5#u8 before = .ok (.Ok (),out,after)) : CompilerInstructionPrefix after := by
  obtain ⟨callback,_,sourceForm,_⟩ := reader_else p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Body.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_open_instructions ops law out.core _ condition form p.current.bt sourceBound held callback

end Itasca.Compiler

end

end

/-! ## EndExitSlots -/

section

/-!
Structured compiler scope-close exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Close Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source scope metadata and retained branch sites preserve instruction
checking through actual nested END, including guard patching. -/
theorem structured_scope_close_exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : FrameExitSlotBounds before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have bound := before.frames.property
    simp only [frames,List.length_append,List.length_singleton] at bound
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have fetchBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := invariant.mode.sites frame (by simp [frames])
  let geometry : ScopeCloseGeometry before :=
    ⟨frame,rest,target,by simpa only [restVal] using frames,rfl,sites.branches.branches⟩
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by omega
  have nonBody : frame.kind ≠ .Body := by
    have kind := shape.kind
    cases form : current.form <;> simp_all [ScopeForm.kind]
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    omega
  apply compiler_scope_close_exit_slots ops law before after state kind bt geometry _ nonBody maps coordinateFits held called
  cases hasIf : frame.if_pc with
  | none =>
    obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
    exact .unguarded hasIf codeFits offsetsFit emitFits
  | some guard =>
    obtain ⟨condition,old,guardCode⟩ := sites.guard guard hasIf
    have nonBody : frame.kind ≠ .Body := by
      intro root
      have body : current.form = .body := by
        have same := shape.kind.symm.trans root
        cases form : current.form <;> simp_all [ScopeForm.kind]
      have guardPosition := shape.guard
      simp only [body,SourceScope.guardPosition,hasIf,Option.map_some] at guardPosition
      cases guardPosition
    exact .guarded guard condition old nonBody hasIf guardCode

end Itasca.Compiler

end

/-! ## Reader End Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 2 END reader supplies progress and a bounded source
endpoint for nested scope recorded exit-slot bounds. -/
theorem reader_nested_end_exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : FrameExitSlotBounds before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    FrameExitSlotBounds after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_exit_slots ops law invariant sourceBound out.core p.current.ctrl.kind
    p.current.bt nonRoot maps held consumed endBound callback

end Itasca.Compiler

end

end

/-! ## EndInstructionPrefix -/

section

/-!
Structured compiler scope-close checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Close Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source scope metadata and retained branch sites preserve instruction
checking through actual nested END, including guard patching. -/
theorem structured_scope_close_open_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have bound := before.frames.property
    simp only [frames,List.length_append,List.length_singleton] at bound
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have fetchBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := invariant.mode.sites frame (by simp [frames])
  let geometry : ScopeCloseGeometry before :=
    ⟨frame,rest,target,by simpa only [restVal] using frames,rfl,sites.branches.branches⟩
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by omega
  have nonBody : frame.kind ≠ .Body := by
    have kind := shape.kind
    cases form : current.form <;> simp_all [ScopeForm.kind]
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    omega
  apply compiler_scope_close_open_instructions ops law before after state kind bt geometry _ nonBody maps coordinateFits held called
  cases hasIf : frame.if_pc with
  | none =>
    obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
    exact .unguarded hasIf codeFits offsetsFit emitFits
  | some guard =>
    obtain ⟨condition,old,guardCode⟩ := sites.guard guard hasIf
    have nonBody : frame.kind ≠ .Body := by
      intro root
      have body : current.form = .body := by
        have same := shape.kind.symm.trans root
        cases form : current.form <;> simp_all [ScopeForm.kind]
      have guardPosition := shape.guard
      simp only [body,SourceScope.guardPosition,hasIf,Option.map_some] at guardPosition
      cases guardPosition
    exact .guarded guard condition old nonBody hasIf guardCode

end Itasca.Compiler

end

/-! ## Reader End Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 2 END reader supplies progress and a bounded source
endpoint for nested scope instruction checking. -/
theorem reader_nested_end_open_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_open_instructions ops law invariant sourceBound out.core p.current.ctrl.kind
    p.current.bt nonRoot maps held consumed endBound callback

end Itasca.Compiler

end

end

/-! ## EnterExitSlots -/

section

/-!
Structured compiler scope-entry exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Entry Exit Slots -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-selected control signatures and live IF layouts establish actual
scope-entry recorded exit-slot bounds, including dormant entries. -/
theorem structured_scope_entry_exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (kind : code.LabelKind) (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (allowed : kind = .Block ∨ kind = .Loop ∨ kind = .Then)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt before.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (ifLayout : kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]))
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨heightFits,sourceFits⟩ := control_entry_coordinates ops before after state ctrl prior kind bt controls valuesFit called
  obtain ⟨codeFits,offsetsFit,mapsFit,framesFit⟩ := invariant.capacities sourceBound
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let makeGeometry (pc : U32) : ScopeEntryGeometry before state bt :=
    ⟨ctrl,prior,signature,pc,controls,selected,valuesFit,heightFits,sourceFits,mapsFit,framesFit⟩
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  by_cases live : before.reachable = true
  · rcases allowed with rfl | rfl | rfl
    · exact compiler_scope_entry_exit_slots ops law before after state .Block bt (makeGeometry pc)
        (.block live rfl) held called
    · exact compiler_scope_entry_exit_slots ops law before after state .Loop bt (makeGeometry pc)
        (.loop live rfl codeFits offsetsFit) held called
    · obtain ⟨stack,layout⟩ := ifLayout rfl live
      let guardedPc : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
      exact compiler_scope_entry_exit_slots ops law before after state .Then bt (makeGeometry guardedPc)
        (.if_ stack layout live rfl codeFits offsetsFit) held called
  · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
    exact compiler_scope_entry_exit_slots ops law before after state kind bt (makeGeometry pc)
      (.dead kind dead rfl) held called

end Itasca.Compiler

end

/-! ## Reader Enter Exit Slots Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve recorded exit-slot
bounds from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (held : FrameExitSlotBounds before)
    (form : Body.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode before = .ok (.Ok (),out,after)) :
    FrameExitSlotBounds after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter p form initialForm
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨signature,selected,_⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls,valuesFit,_,_⟩ := post.front initialForm
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have called : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (),after) := by
    rcases initialForm with rfl | rfl | rfl <;> exact callback
  have ifLayout : form.kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]) := by
    intro thenKind live
    have formThen : form = .then_ := by
      rcases initialForm with rfl | rfl | rfl <;> simp_all [Body.Frames.Form.kind]
    have layout := (invariant.live live).2.layout
    obtain ⟨front,_,oldTypes,_,_,_,_,_,_,_,_⟩ := post.callback_inputs initialForm
      (reach.current live) (invariant.known live) layout signatures
    refine ⟨front ++ ins.map Translation.valueType,?_⟩
    simpa only [oldTypes,formThen,Body.Frames.Form.args,List.append_assoc] using layout
  apply structured_scope_entry_exit_slots ops law invariant sourceBound out.core
    (Body.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout held called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Body.Frames.Form.kind]

end Itasca.Compiler

end

end

/-! ## StructuredRootMapPublication -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A reached root prefix supplies its sole body frame and branch sites. The
actual final END emits RETURN and establishes every strict map range checked
at publication, rather than assuming those ranges in a completed certificate. -/
theorem structured_root_map_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals [] current raw position)
    (rootForm : current.form = .body) (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (maps : ControlMapPublication before) (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FinalControlMapBounds after.function := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have empty : prior = [] := by cases paired; rfl
  let rest := alloc.vec.Vec.new runtime.compiler.Frame
  have restEmpty : rest.val = [] := by simp [rest,alloc.vec.Vec.new]
  have physical : before.frames.val = rest.val ++ [frame] := by simpa only [restEmpty,empty] using frames
  have root : frame.kind = .Body := by simpa only [rootForm,ScopeForm.kind] using shape.kind
  have noIf : frame.if_pc = none := by
    have guard := shape.guard
    simpa only [rootForm,SourceScope.guardPosition,Option.map_eq_none_iff] using guard
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have endFits : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by omega
  have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
  exact compiler_root_map_publication ops law before after state frame rest target maps physical restEmpty root noIf
    rfl sites shape.mapBound coordinateFits codeFits offsetsFit emitFits progress endBound called

end Itasca.Compiler

end

end

/-! ## RootMapPublication -/

section

/-! ## EndPublication -/

section

/-!
Structured compiler scope-close source map publication and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Close Publication -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A reached prefix supplies the physical closing frame and all branch and
guard sites. Reader progress and the declared body extent establish the new
source interval; the argument does not require an already accepted map check. -/
theorem structured_scope_close_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have bound := before.frames.property
    simp only [frames,List.length_append,List.length_singleton] at bound
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have fetchBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := invariant.mode.sites frame (by simp [frames])
  let geometry : ScopeCloseGeometry before :=
    ⟨frame,rest,target,by simpa only [restVal] using frames,rfl,sites.branches.branches⟩
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by omega
  apply compiler_scope_close_publication ops law before after state kind bt geometry _ coordinates maps inside progress endBound called
  cases hasIf : frame.if_pc with
  | none =>
    obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
    exact .unguarded hasIf codeFits offsetsFit emitFits
  | some guard =>
    obtain ⟨condition,old,guardCode⟩ := sites.guard guard hasIf
    have nonBody : frame.kind ≠ .Body := by
      intro root
      have body : current.form = .body := by
        have same := shape.kind.symm.trans root
        cases form : current.form <;> simp_all [ScopeForm.kind]
      have guardPosition := shape.guard
      simp only [body,SourceScope.guardPosition,hasIf,Option.map_some] at guardPosition
      cases guardPosition
    exact .guarded guard condition old nonBody hasIf guardCode

end Itasca.Compiler

end

/-! ## Reader End Publication -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 2 END reader supplies progress and a bounded source
endpoint for both nested scope closing and final function closing. -/
theorem reader_end_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_publication ops law invariant sourceBound out.core p.current.ctrl.kind
    p.current.bt coordinates maps consumed endBound callback

end Itasca.Compiler

end

end

/-! ## EnterPublication -/

section

/-!
Structured compiler scope-entry source map publication and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Entry Publication -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A reached structured prefix supplies entry PC and reserve bounds. Actual
checked entry supplies arithmetic bounds, including dormant stack heights.
The reader contributes only its selected control/signature and live IF stack. -/
theorem structured_scope_entry_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (kind : code.LabelKind) (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (allowed : kind = .Block ∨ kind = .Loop ∨ kind = .Then)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt before.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (ifLayout : kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]))
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨heightFits,sourceFits⟩ := control_entry_coordinates ops before after state ctrl prior kind bt controls valuesFit called
  obtain ⟨codeFits,offsetsFit,mapsFit,framesFit⟩ := invariant.capacities sourceBound
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let makeGeometry (pc : U32) : ScopeEntryGeometry before state bt :=
    ⟨ctrl,prior,signature,pc,controls,selected,valuesFit,heightFits,sourceFits,mapsFit,framesFit⟩
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  by_cases live : before.reachable = true
  · rcases allowed with rfl | rfl | rfl
    · exact compiler_scope_entry_publication ops law before after state .Block bt (makeGeometry pc)
        (.block live rfl) coordinates maps inside forward called
    · exact compiler_scope_entry_publication ops law before after state .Loop bt (makeGeometry pc)
        (.loop live rfl codeFits offsetsFit) coordinates maps inside forward called
    · obtain ⟨stack,layout⟩ := ifLayout rfl live
      let guardedPc : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
      exact compiler_scope_entry_publication ops law before after state .Then bt (makeGeometry guardedPc)
        (.if_ stack layout live rfl codeFits offsetsFit) coordinates maps inside forward called
  · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
    exact compiler_scope_entry_publication ops law before after state kind bt (makeGeometry pc)
      (.dead kind dead rfl) coordinates maps inside forward called

end Itasca.Compiler

end

/-! ## Reader Enter Publication Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve both publication
invariants from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : BodyReaderReachability before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (form : Body.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter p form initialForm
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨signature,selected,_⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls,valuesFit,_,_⟩ := post.front initialForm
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := post.after.2.1
    omega
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by
    have cursor := invariant.cursor
    have bounded := p.inbounds
    change p.start.val < data.length at bounded
    omega
  have called : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (),after) := by
    rcases initialForm with rfl | rfl | rfl <;> exact callback
  have ifLayout : form.kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]) := by
    intro thenKind live
    have formThen : form = .then_ := by
      rcases initialForm with rfl | rfl | rfl <;> simp_all [Body.Frames.Form.kind]
    have layout := (invariant.live live).2.layout
    obtain ⟨front,_,oldTypes,_,_,_,_,_,_,_,_⟩ := post.callback_inputs initialForm
      (reach.current live) (invariant.known live) layout signatures
    refine ⟨front ++ ins.map Translation.valueType,?_⟩
    simpa only [oldTypes,formThen,Body.Frames.Form.args,List.append_assoc] using layout
  apply structured_scope_entry_publication ops law invariant sourceBound out.core
    (Body.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout coordinates maps inside _ called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Body.Frames.Form.kind]
  · exact le_trans invariant.cursor (Nat.le_of_lt consumed)

end Itasca.Compiler

end

end

/-! ## RootMapPublication -/

section

/-!
Actual Wasm 2 root END establishes the strict final map checker bounds. The source zipper and empty returned control stack identify the sole root frame.

Main declarations: `reader_root_map_publication`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem source_body_form {bt : signature.BlockType} {form : ScopeForm}
    (matched : ScopeFormMatches bt form .body) : form = .body := by
  cases matched
  rfl

/-- Actual Wasm 2 root END establishes the strict final map checker bounds.
The source zipper and empty returned control stack identify the sole root frame. -/
theorem reader_root_map_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Body.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (closed : out.core.ctrls.val = [])
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    FinalControlMapBounds after.function ∧ SourceAligned after := by
  obtain ⟨callback,_,_,_,zipper,afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have root : p.current.form = .body ∧ p.parents = [] := by
    rcases zipper with ⟨root,empty,_⟩ | ⟨grandparents,parent,instruction,split,finished,opened⟩
    · exact ⟨root,empty⟩
    · obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := opened
      rw [controls] at closed
      simp at closed
  have parentsEmpty : parents = [] := by
    have paired := same.parents
    rw [root.2] at paired
    cases paired
    rfl
  have rootForm : current.form = .body := by
    have matched := same.current.form
    rw [root.1] at matched
    exact source_body_form matched
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  rw [parentsEmpty] at invariant
  refine ⟨structured_root_map_publication ops law invariant rootForm sourceBound out.core p.current.ctrl.kind
    p.current.bt maps consumed endBound callback,?_⟩
  exact (compiler_end_sources ops law before after out.core p.current.ctrl.kind p.current.bt callback).aligned invariant.sources

end Itasca.Compiler

end

end
