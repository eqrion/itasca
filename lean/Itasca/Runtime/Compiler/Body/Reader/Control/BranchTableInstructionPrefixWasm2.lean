import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSourceTransferBounds
import Itasca.Runtime.Compiler.Local.Checking.TableCallbackExitSlots
import Itasca.Runtime.Compiler.Local.Checking.TableCallbackInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableDecodePrefix
import Itasca.Runtime.Compiler.Local.Source.SourceBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableBoundary
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableInputsWasm2

/-!
Checked br_table reader instructions, including scratch-slot bounds and instruction-room requirements.
-/

/-! ## Source Table Scratch Exit Slots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Typed labels and a source transfer intervals discharge the actual complete
table callback, including the fallback, scratch clearing, and observation. -/
theorem StructuredCompilerPrefix.br_table_scratch_exit_slots
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget0 : runtime.compiler.Budget A) (buffer : alloc.vec.Vec U32)
    (state : code.OpIterState) (fallback : U32) (view : signature.ResultType)
    (labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes raw = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧
        stack = scope.front++discarded++scope.branchTypes)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops {before with budget := budget0,table_depths := buffer} state fallback view = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  apply compiler_br_table_callback_exit_slots ops law {before with budget := budget0,table_depths := buffer} after state fallback view
    (held.retained rfl le_rfl) _ called
  intro labeled labelCalled live lowered lowerCalled
  obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law {before with budget := budget0,table_depths := buffer} labeled state fallback labelCalled
  subst labeled
  change depths.val = buffer.val++[fallback] at appended
  change before.reachable = true at live
  obtain ⟨stack,input,typedLabels⟩ := labels live
  have layout := (invariant.live live).2.layout
  rw [input] at layout
  have geometry := invariant.table_transfer_geometry live input typedLabels
  apply compiler_lower_table_exit_slots ops law {before with budget,table_depths := depths} lowered ?transfers (layout.capacity live)
    (held.retained rfl le_rfl) lowerCalled
  · intro depth member index frame found position
    change depth ∈ depths.val at member
    rw [appended] at member
    exact geometry depth member index frame found position

end Itasca.Runtime.Compiler

end

/-! ## Source Table Scratch Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Typed labels and a source-paid stub budget discharge the actual complete
table callback, including the fallback, scratch clearing, and observation. -/
theorem StructuredCompilerPrefix.br_table_scratch_open_instructions
    {jumpTables : List U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current raw position)
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget0 : runtime.compiler.Budget A) (buffer : alloc.vec.Vec U32)
    (state : code.OpIterState) (fallback : U32) (view : signature.ResultType)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (room : before.function.code.val.length+1+2*(buffer.val.length+1) ≤ Usize.max)
    (tables : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes raw = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧
        stack = scope.front++discarded++scope.branchTypes)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops {before with budget := budget0,table_depths := buffer} state fallback view = .ok (.Ok (),after)) : CompilerInstructionPrefix after := by
  apply compiler_br_table_callback_open_instructions ops law {before with budget := budget0,table_depths := buffer} after state fallback view
    (held.retained rfl rfl) _ called
  intro labeled labelCalled live lowered lowerCalled
  obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law {before with budget := budget0,table_depths := buffer} labeled state fallback labelCalled
  subst labeled
  change depths.val = buffer.val++[fallback] at appended
  change before.reachable = true at live
  obtain ⟨stack,input,typedLabels⟩ := labels live
  have layout := (invariant.live live).2.layout
  rw [input] at layout
  have stagedLayout : CompilerLayout {before with budget,table_depths := depths} (stack++[.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  have geometry := invariant.table_transfer_geometry live input typedLabels
  apply compiler_lower_table_open_instructions ops law _ lowered stack stagedLayout invariant.sources
    ?depths fixups ?room tables coordinate ?nonempty ?transfers (layout.capacity live)
    (held.retained rfl rfl) lowerCalled
  · intro depth member
    change depth ∈ depths.val at member
    rw [appended] at member
    obtain ⟨scope,discarded,selected,targetStack⟩ := typedLabels depth member
    obtain ⟨index,frame,_,_,_,position,_⟩ :=
      invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
    change depth.val < before.frames.val.length
    omega
  · change before.function.code.val.length+1+2*depths.val.length ≤ Usize.max
    rw [appended,List.length_append,List.length_singleton]
    exact room
  · change 0 < depths.val.length
    rw [appended,List.length_append,List.length_singleton]
    omega
  · intro depth member index frame found position
    change depth ∈ depths.val at member
    rw [appended] at member
    exact geometry depth member index frame found position

end Itasca.Runtime.Compiler

end

/-! ## Table Instruction Room -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem table_source_word_room : 3*limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
  norm_num [limits.MAX_MODULE_BYTES]
  scalar_tac

/-- Source bytes pay for the dispatch and two words per arm. This bound holds
for every permitted usize width and does not assume a 64-bit target. -/
theorem table_instruction_room {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data : Slice U8} {start finish : Usize} {depths : List U32} {fallback : U32} {position : Nat}
    (budget : SourceCodeBudget compiler position) (consumed : position < start.val)
    (decoded : BrTable.Decoded data start depths fallback finish)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length+1+2*(depths.length+1) ≤ Usize.max := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countSpan := countDecoded.span
  have labelSpan := table_labels_length_span labels
  have defaultSpan := defaultDecoded.span
  change compiler.function.code.val.length ≤ 3*position at budget
  have paid : compiler.function.code.val.length+1+2*(depths.length+1) ≤ 3*data.length := by omega
  exact paid.trans ((Nat.mul_le_mul_left 3 sourceBound).trans table_source_word_room)

end Itasca.Runtime.Compiler

end

/-! ## Reader Table Instruction Prefix Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual Wasm 2 label collection and the complete table callback preserve
instruction checks and recorded exit-slot bounds from independently typed labels. -/
theorem reader_table_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (final : code.BodyState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (boundary : CompilerTableBoundary before)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before = .ok (.Ok (),final,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,view,last,readState,budget,buffer,
      countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,countEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env _ accepted
  have popFacts := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at popFacts
  have popPosition : popped.pos = first := popFacts.2.2.1
  rw [popPosition] at labelsDecoded
  have encoded : BrTable.Decoded data st.core.pos depths fallback readState.core.pos :=
    ⟨count,first,last,countDecoded,countEq,labelsDecoded,defaultDecoded⟩
  have bufferSource : buffer.val = depths := by simpa only [boundary.depths,List.nil_append] using bufferEq
  have labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes st.core.vals.val = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧ stack = scope.front++discarded++scope.branchTypes := by
    intro live
    obtain ⟨stack,input,scopes⟩ := reader_table_inputs_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      (invariant.live live).1 (invariant.known live) (monomorphic live) before after final depths fallback
      readState.core.pos encoded accepted
    refine ⟨stack,input,?_⟩
    intro depth member
    rw [bufferSource] at member
    obtain ⟨scope,discarded,selected,_,stackEq⟩ := scopes depth member
    refine ⟨scope,discarded,?_,stackEq⟩
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
  have coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  have room : before.function.code.val.length+1+2*(buffer.val.length+1) ≤ Usize.max := by
    rw [bufferSource]
    exact table_instruction_room invariant.codeBudget (by have position := p.pos; omega) encoded sourceBound
  exact ⟨invariant.br_table_scratch_open_instructions ops law budget buffer final.core fallback view
      fixups room boundary.targets coordinate labels held callback,
    invariant.br_table_scratch_exit_slots ops law budget buffer final.core fallback view labels exits callback⟩

end Itasca.Runtime.Compiler

end
