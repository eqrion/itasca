import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.IndependentBodyDemand
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Checking.InstructionBounds
import Itasca.Runtime.Compiler.Body.Reader.Control.TerminalCompilationAndSafety
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlInstructionPrefixes
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndElseCompilation
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety
import Itasca.Runtime.Compiler.Local.Coordinates.InstructionTargetEffects
import Itasca.Runtime.Compiler.Local.Publication.ScalarAndTablePublication
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Body.Trace.BytesDispatch
import Itasca.Body.Visitor.ReachedTableLoop
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableAvailability
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Capacity.ConditionalAndSimdAvailability
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects BranchTablePublication, ReachedControlAcceptance, SourceBoundControlAcceptance.
Each section documents its contracts and consumers.
-/

/-! ## BranchTablePublication -/

section

open Itasca.Representation

/-!
# Branch Table Publication

Control capacity, branch-table transfers, scope entry and root closure preserve checked emitted prefixes. The resulting coordinate bounds support branch-table and control-map publication.
-/

/-! ## SourceControlCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independent control-reader success and its retained source suffix supply
all instruction, control, operand, reserve, slot, and end-coordinate demands.
No compiler callback success or caller-supplied capacity record is needed. -/
theorem IndexedTableReaderCompilerPoint.control_capacity_from_source {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState) (bound : Nat)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
    (reference : code.step_body recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    CallbackCapacity compiler out.core bound 3 ∧ ScopeDemand compiler out.core bound ∧
      compiler.function.body_start.val+out.core.pos.val ≤ Usize.max ∧ st.core.pos.val < out.core.pos.val := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨observations,_,trace⟩ := kind.records pending recorder id recorder_records ⟨sourceLocals,ft.results⟩
    byte before (.Ok ()) out after canonical
  obtain ⟨token,chunk⟩ := trace.accepted
  have endBound := chunk.encoded.span
  change st.core.pos.val < out.core.pos.val ∧ out.core.pos.val ≤ data.length at endBound
  rw [kind.dispatch] at canonical
  obtain ⟨value,_,called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ canonical
  have operands := (source_callback_demand before after final out.core (kind.action value) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index (.Ok ()) called tail).1
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor (bytes := 1) (count := 3) (by omega) (by decide) out.core operands
  have scope := room.scope budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor state.compiled.controlBudget inbounds out.core operands
  obtain ⟨_,_,_,_,_,_,_,bodyStart,_⟩ := state.compiled.metadata.fields
  refine ⟨capacity,scope,?_,endBound.1⟩
  rw [bodyStart]
  have coordinate := room.coordinate
  omega

end Itasca.Compiler

end

/-! ## TerminalInstructionPrefix -/

section

/-!
Actual source RETURN checks its full result suffix and retains recorded exits.

Main declarations: `reader_return_open_instructions` and `reader_unreachable_open_instructions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual source RETURN checks its full result suffix and retains recorded exits. -/
theorem reader_return_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions (p.ft.results.val.map Translation.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨callback, read, values, post⟩ := reader_return p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  refine ⟨?_,(compiler_return_ordinary_result ops law before after out.core (.Ok ()) callback).exit_slots exits⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack st out env index p.ft.results.val outer p.current.vals
      (by simp [Body.resolve, p.signature]) vals (by simpa [Body.Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Body.Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    have layout := (invariant.live reachable).2.layout
    have capacity := layout.capacity reachable
    rw [input] at layout
    have bounded : slots (compilerLocals before)+slots front < 2^32 := by
      have bound := before.height.hBounds
      change before.height.val < 2^32 at bound
      rw [layout.height,slots_append] at bound
      omega
    let source : U32 := UScalar.ofNatCore (slots (compilerLocals before)+slots front) bounded
    have sourcePosition : source.val = slots (compilerLocals before)+slots front := rfl
    have height : before.height.val = source.val+frame.results.val := by
      rw [layout.height,slots_append,sourcePosition,resultWidth]
      omega
    exact compiler_return_live_open_instructions ops law before after out.core frame source reachable found height capacity
      codeFits sourceFits coordinateFits held callback
  · exact compiler_return_dead_open_instructions ops law before after out.core (Bool.eq_false_iff.mpr reachable) held callback

/-- Actual trap reading preserves all earlier checks and emits a checked trap word when live. -/
theorem reader_unreachable_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities sourceBound
  have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  exact ⟨compiler_unreachable_open_instructions ops law before after out.core codeFits sourceFits coordinateFits held callback,
    (compiler_unreachable_ordinary_result ops law before after out.core (.Ok ()) callback).exit_slots exits⟩

end Itasca.Compiler

end

/-! ## BranchTableSourceTransferBounds -/

section

/-!
Source typing of every table label supplies overlap-safe transfer bounds and already opened loop targets, including repeated and outer labels.

Main declarations: `StructuredCompilerPrefix.table_transfer_geometry`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source typing of every table label supplies overlap-safe transfer bounds
and already opened loop targets, including repeated and outer labels. -/
theorem StructuredCompilerPrefix.table_transfer_geometry
    {jumpTables : List U32} {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position stack} {depths : List U32}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current raw position)
    (live : compiler.reachable = true)
    (input : Body.Stack.stackTypes raw = stack++[.I32])
    (labels : ∀ depth ∈ depths, ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      stack = scope.front++discarded++scope.branchTypes) :
    ∀ depth ∈ depths, ∀ (index : Usize) (frame : runtime.compiler.Frame),
      compiler.frames.val[index.val]? = some frame → index.val+depth.val+1 = compiler.frames.val.length →
      frame.height.val+(frameBranchWidth frame).val+1 ≤ compiler.height.val ∧
        (frame.kind = .Loop → frame.start_pc.val ≤ compiler.function.code.length) := by
  intro depth member index frame found position
  obtain ⟨scope,discarded,selected,targetStack⟩ := labels depth member
  obtain ⟨actual,actualFrame,source,condition,actualFound,actualPosition,shape,height,sourceAt,sourceWidth,_⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have same : actual = index := UScalar.eq_of_val_eq (by omega)
  subst actual
  rw [found] at actualFound
  cases Option.some.inj actualFound
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by
    rw [slots_append]
    omega
  refine ⟨by omega,?_⟩
  intro loop
  have kind := shape.kind
  have start := shape.start
  have entry := shape.entryBound
  cases form : scope.form <;> simp_all [ScopeForm.kind,SourceScope.frameStart]

end Itasca.Compiler

end

/-! ## BranchTableInstructionPrefix -/

section

/-!
Checked br_table reader instructions, including scratch-slot bounds and instruction-room requirements.
-/

/-! ## Source Table Scratch Exit Slots -/

section

namespace Itasca.Compiler
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
      Body.Stack.stackTypes raw = stack++[.I32] ∧
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

end Itasca.Compiler

end

/-! ## Source Table Scratch Instruction Prefix -/

section

namespace Itasca.Compiler
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
      Body.Stack.stackTypes raw = stack++[.I32] ∧
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

end Itasca.Compiler

end

/-! ## Table Instruction Room -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem table_source_word_room : 3*limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
  norm_num [limits.MAX_MODULE_BYTES]
  scalar_tac

/-- Source bytes pay for the dispatch and two words per arm. This bound holds
for every permitted usize width and does not assume a 64-bit target. -/
theorem table_instruction_room {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data : Slice U8} {start finish : Usize} {depths : List U32} {fallback : U32} {position : Nat}
    (budget : SourceCodeBudget compiler position) (consumed : position < start.val)
    (decoded : Body.BrTable.Decoded data start depths fallback finish)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length+1+2*(depths.length+1) ≤ Usize.max := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countSpan := countDecoded.span
  have labelSpan := table_labels_length_span labels
  have defaultSpan := defaultDecoded.span
  change compiler.function.code.val.length ≤ 3*position at budget
  have paid : compiler.function.code.val.length+1+2*(depths.length+1) ≤ 3*data.length := by omega
  exact paid.trans ((Nat.mul_le_mul_left 3 sourceBound).trans table_source_word_room)

end Itasca.Compiler

end

/-! ## Reader Table Instruction Prefix Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual Wasm 2 label collection and the complete table callback preserve
instruction checks and recorded exit-slot bounds from independently typed labels. -/
theorem reader_table_open_instructions {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (final : code.BodyState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (boundary : CompilerTableBoundary before)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,view,last,readState,budget,buffer,
      countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,countEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  have popFacts := code.pop_with_type.total {st.core with pos := first} .I32
    (show Body.Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at popFacts
  have popPosition : popped.pos = first := popFacts.2.2.1
  rw [popPosition] at labelsDecoded
  have encoded : Body.BrTable.Decoded data st.core.pos depths fallback readState.core.pos :=
    ⟨count,first,last,countDecoded,countEq,labelsDecoded,defaultDecoded⟩
  have bufferSource : buffer.val = depths := by simpa only [boundary.depths,List.nil_append] using bufferEq
  have labels : before.reachable = true → ∃ stack,
      Body.Stack.stackTypes st.core.vals.val = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧ stack = scope.front++discarded++scope.branchTypes := by
    intro live
    obtain ⟨stack,input,scopes⟩ := reader_table_inputs
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

end Itasca.Compiler

end

end

/-! ## EnterInstructionPrefix -/

section

/-!
Structured compiler scope-entry checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Entry Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-selected control signatures and live IF layouts establish actual
scope-entry instruction checking, including dormant entries. -/
theorem structured_scope_entry_open_instructions {jumpTables : List U32}
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
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨heightFits,sourceFits⟩ := control_entry_coordinates ops before after state ctrl prior kind bt controls valuesFit called
  obtain ⟨codeFits,offsetsFit,mapsFit,framesFit⟩ := invariant.capacities sourceBound
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let makeGeometry (pc : U32) : ScopeEntryGeometry before state bt :=
    ⟨ctrl,prior,signature,pc,controls,selected,valuesFit,heightFits,sourceFits,mapsFit,framesFit⟩
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  by_cases live : before.reachable = true
  · rcases allowed with rfl | rfl | rfl
    · exact compiler_scope_entry_open_instructions ops law before after state .Block bt (makeGeometry pc)
        (.block live rfl) held called
    · exact compiler_scope_entry_open_instructions ops law before after state .Loop bt (makeGeometry pc)
        (.loop live rfl codeFits offsetsFit) held called
    · obtain ⟨stack,layout⟩ := ifLayout rfl live
      let guardedPc : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
      exact compiler_scope_entry_open_instructions ops law before after state .Then bt (makeGeometry guardedPc)
        (.if_ stack layout live rfl codeFits offsetsFit) held called
  · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
    exact compiler_scope_entry_open_instructions ops law before after state kind bt (makeGeometry pc)
      (.dead kind dead rfl) held called

end Itasca.Compiler

end

/-! ## Reader Enter Instruction Prefix Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve instruction
checks from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_open_instructions {jumpTables : List U32}
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
    (held : CompilerInstructionPrefix before)
    (form : Body.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after := by
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
  apply structured_scope_entry_open_instructions ops law invariant sourceBound out.core
    (Body.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout held called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Body.Frames.Form.kind]

end Itasca.Compiler

end

end

/-! ## RootInstructionPrefix -/

section

/-!
Structured compiler root closure checked instructions and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Root Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source root geometry, the preceding live stack, and branch exits discharge every
stored instruction check at actual function close. The final return's capacity
comes from the retained slot bounds and prepared local region. -/
theorem structured_root_checked_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals [] current raw position)
    (rootForm : current.form = .body) (entered : current.entered = true)
    (front : current.front = []) (results : current.results = returns)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (normal : before.reachable = true → Body.Stack.stackTypes raw = returns)
    (exits : ∀ frame ∈ before.frames.val, frame.end_reachable = true →
      frame.height.val+frame.results.val ≤ before.function.slot_count.val)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have empty : prior = [] := by cases paired; rfl
  let rest := alloc.vec.Vec.new runtime.compiler.Frame
  have restEmpty : rest.val = [] := by simp [rest,alloc.vec.Vec.new]
  have physical : before.frames.val = rest.val++[frame] := by simpa only [restEmpty,empty] using frames
  have root : frame.kind = .Body := by simpa only [rootForm,ScopeForm.kind] using shape.kind
  have noIf : frame.if_pc = none := by
    have guard := shape.guard
    simpa only [rootForm,SourceScope.guardPosition,Option.map_eq_none_iff] using guard
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  let geometry : ScopeCloseGeometry before := ⟨frame,rest,target,physical,rfl,sites⟩
  have stable := invariant.metadata.trans (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called)
  have localLayout := stable.local_layout initialLayout
  obtain ⟨_,_,_,_,localsEq,_,slotsEq,_⟩ := stable.fields
  have localTypes : compilerLocals after = locals := by simpa only [compilerLocals,localsEq] using initialLocals
  have localCapacity : after.function.local_slots.val ≤ after.function.slot_count.val := by
    rw [slotsEq]
    exact initialCapacity.trans stable.capacity
  have height : frame.height = after.function.local_slots := by
    apply UScalar.eq_of_val_eq
    rw [localLayout.slots,localTypes]
    simpa only [front,slots,Nat.add_zero] using shape.height entered
  have width : frame.results.val = slots returns := by simpa only [results] using shape.results
  obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have endFits : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have returnFits : frame.height.val+
      (if scopeExitLive before.reachable frame then frame.results else 0#u32).val ≤ after.function.slot_count.val := by
    have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    by_cases live : before.reachable = true
    · have layout := (invariant.live live).2.layout
      have bound := layout.live_slots_fit live
      have localsMatch := (invariant.live live).2.localsEq
      rw [normal live,localsMatch,← width] at bound
      have heightBefore : frame.height.val = slots locals := by
        simpa only [front,slots,Nat.add_zero] using shape.height entered
      rw [← heightBefore] at bound
      simpa [scopeExitLive,live,root] using bound.trans capacity
    · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
      by_cases exit : frame.end_reachable = true
      · have bound := exits frame (by simp [frames]) exit
        simpa [scopeExitLive,dead,root,exit] using bound.trans capacity
      · have noExit : frame.end_reachable = false := by cases reachable : frame.end_reachable <;> simp_all
        simpa [scopeExitLive,dead,root,noExit,height] using localCapacity
  refine ⟨compiler_root_close_checked_instructions_of_slots ops law before after state kind bt geometry root restEmpty noIf
    codeFits offsetsFit (by omega) (by omega) maps held returnFits called,?_⟩
  have effect := close_function_effect ops law before state frame rest target physical root noIf rfl sites shape.mapBound
    (by omega) codeFits offsetsFit (by omega)
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,_,_,_⟩ := effect rfl
  rw [frames]
  exact restEmpty

end Itasca.Compiler

end

/-! ## Reader Root Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual root END checks every stored instruction from its typed preceding stack and retained exits. -/
theorem StructuredReaderCompilerState.root_checked_instructions {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions (ft.results.val.map Translation.valueType) locals
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
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Body.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Body.outputs, Body.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Body.Stack.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Body.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translation.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Body.Stack.stackTypes st.core.vals.val = ft.results.val.map Translation.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Body.Stack.Realizes false savedCurrent.vals (savedCurrent.outs.map Translation.valueType) := by
      simpa [p, ReaderBoundary.pending, mono] using realizes
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

end Itasca.Compiler

end

end

/-! ## ControlCheckedPrefix -/

section

/-!
All control-reader forms preserve instruction and exit-slot checking at an actual Wasm 2 source boundary. Root END additionally checks the completed code before the final compiler publication check is called.

Main declarations: `StructuredReaderCompilerState.control_checked_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- All control-reader forms preserve instruction and exit-slot checking at
an actual Wasm 2 source boundary. Root END additionally checks the completed
code before the final compiler publication check is called. -/
theorem StructuredReaderCompilerState.control_checked_prefix
    {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions
      (ft.results.val.map Translation.valueType) locals data env sourceLocals index ft st
      parents current savedParents savedCurrent)
    (ctx : code.Context) (contextSource : ctx.locals = sourceLocals) (C : context)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (metadata : FunctionParameterSlots before env) (signatures : SignatureSequence before.signatures.val env.types.val)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (maps : ControlMapPublication before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (kind : ControlReaderKind)
    (byte : data.val[st.core.pos.val]'inbounds = kind.opcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  let p := state.boundary.pending next advance inbounds
  have sourceBound := state.boundary.source_bound
  have positionBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  have coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := state.compiled.cursor
    omega
  cases kind with
  | block =>
    refine ⟨reader_enter_open_instructions p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .block (.inl rfl) ?_ ?_,
      reader_enter_exit_slots p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .block (.inl rfl) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,Body.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Body.Frames.Form.opcode] using accepted
  | loop =>
    refine ⟨reader_enter_open_instructions p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .loop (.inr (.inl rfl)) ?_ ?_,
      reader_enter_exit_slots p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .loop (.inr (.inl rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,Body.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Body.Frames.Form.opcode] using accepted
  | if_ =>
    refine ⟨reader_enter_open_instructions p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .then_ (.inr (.inr rfl)) ?_ ?_,
      reader_enter_exit_slots p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .then_ (.inr (.inr rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,Body.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Body.Frames.Form.opcode] using accepted
  | else_ =>
    exact ⟨reader_else_open_instructions p ops law initial before after out ctx state.compiled state.sources held byte accepted,
      reader_else_exit_slots p ops law initial before after out ctx state.compiled state.sources state.fronts state.reach.current exits byte accepted⟩
  | br =>
    exact ⟨reader_br_open_instructions p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound fixups coordinate held (by simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_exit_slots p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current exits (by simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | br_if =>
    exact ⟨reader_br_if_open_instructions p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound held (by simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_if_exit_slots p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound exits (by simpa only [p,ReaderBoundary.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | return_ =>
    exact reader_return_open_instructions p ops law initial before after out ctx state.compiled state.sources
      state.reach.current sourceBound bodyBound held exits byte accepted
  | call =>
    exact reader_call_checked_prefix p ops law initial before after out ctx state.compiled metadata
      state.reach.current sourceBound bodyBound held exits byte accepted
  | call_indirect =>
    exact reader_indirect_call_checked_prefix p ops law initial before after out ctx state.compiled C matched contextLocals signatures
      state.reach.current sourceBound bodyBound held exits byte accepted
  | end_ =>
    by_cases root : savedCurrent.form = .body
    · obtain ⟨parentsEmpty,savedEmpty⟩ := state.root_scopes root
      subst parents savedParents
      have canonicalState := state
      rw [← contextSource] at canonicalState
      obtain ⟨checked,empty⟩ := canonicalState.root_checked_instructions (ctx := ctx) ops law root next advance inbounds out sourceBound
        bodyExtent initialLayout initialLocals initialCapacity maps held exits byte accepted
      constructor
      · intro index instruction found
        exact .checked (checked instruction (List.mem_of_getElem? found))
      · intro frame member
        rw [empty] at member
        simp at member
    · have nonRoot : current.form ≠ .body := by
        intro form
        have matching := state.sources.current.form
        rw [form] at matching
        have savedBody : savedCurrent.form = .body := by
          generalize savedEq : savedCurrent.form = actual at matching
          cases matching
          rfl
        exact root savedBody
      exact ⟨reader_nested_end_open_instructions p ops law initial before after out ctx types functions _ locals parents current
          state.compiled nonRoot maps held bodyExtent byte accepted,
        reader_nested_end_exit_slots p ops law initial before after out ctx types functions _ locals parents current
          state.compiled nonRoot maps exits bodyExtent byte accepted⟩

end Itasca.Compiler

end

/-! ## ClosedInstructionPrefix -/

section

/-!
Closing the actual reader control stack publishes checks for every stored instruction.

Main declarations: `StructuredReaderCompilerState.closed_checked_instructions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Closing the actual reader control stack publishes checks for every stored instruction. -/
theorem StructuredReaderCompilerState.closed_checked_instructions
    {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types functions
      (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (closed : out.core.ctrls.val = [])
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    CheckedInstructionPrefix after.function := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback,read,encoded,realizes,zipper,afterState⟩ := reader_end p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have root : p.current.form = .body := by
    rcases zipper with ⟨root,empty,_⟩ | ⟨grandparents,parent,instruction,split,finished,opened⟩
    · exact root
    · obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := opened
      rw [controls] at closed
      simp at closed
  have root : savedCurrent.form = .body := by
    simpa only [p,ReaderBoundary.pending] using root
  obtain ⟨parentsEmpty,savedEmpty⟩ := state.root_scopes root
  subst parents savedParents
  exact (state.root_checked_instructions (ctx := ctx) ops law root next advance inbounds out state.boundary.source_bound
    bodyExtent initialLayout initialLocals initialCapacity maps held exits byte accepted).1

end Itasca.Compiler

end

/-! ## BranchTablePublication -/

section

/-!
Actual Wasm 2 table decoding, selector handling and label collection retain publication bounds before its final table callback.

Main declarations: `reader_table_publication`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual Wasm 2 table decoding, selector handling and label collection retain
publication bounds before its final table callback. -/
theorem reader_table_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ final.core.pos.val)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  exact ⟨compiler_br_table_source_coordinates ops law {before with budget,table_depths := buffer} after final.core fallback
      types (by simpa only [SourceCoordinates] using coordinates) inside forward callback,
    compiler_br_table_map_publication ops law {before with budget,table_depths := buffer} after final.core fallback
      types (maps.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) forward callback⟩

end Itasca.Compiler

end

end

/-! ## ReachedControlAcceptance -/

section

open Itasca.Representation

/-!
# Reached Control Acceptance

Reached branch-table and control-entry states supply the premises for instruction acceptance at the selected source point.
-/

/-! ## BranchTableSourceBoundAcceptance -/

section

/-!
Source-bounded br_table reader replay. Label-collection invariants, loop framing and callback availability establish successful compilation from the independent source demand.
-/

/-! ## Label Collection Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Collected labels change only scratch storage and budget counters. The
resource allowance is indexed by source labels, independent of emitted code. -/
def LabelCollectionPrefix {A : Type} (initial current : runtime.compiler.FunctionCompiler A)
    (count : Nat) : Prop :=
  ∃ budget depths, current = {initial with budget,table_depths := depths} ∧
    depths.length = initial.table_depths.length+count ∧
    CompilationBudgetEffect initial.budget budget (fun counter => if counter = .branches then count else 0)

theorem LabelCollectionPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    LabelCollectionPrefix compiler compiler 0 := by
  exact ⟨compiler.budget,compiler.table_depths,rfl,by omega,by
    simpa using CompilationBudgetEffect.refl compiler.budget⟩

/-- The actual next label accepts from the unconsumed portion of independently
bounded scratch and branch demand. All other compiler fields are retained. -/
theorem LabelCollectionPrefix.collect_available {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (depth : U32)
    (count total : Nat) (held : LabelCollectionPrefix initial compiler count) (remaining : count < total)
    (branches : initial.budget.branches.val+total ≤ initial.budget.limits.max_branch_table_entries.val)
    (capacity : initial.table_depths.length+total ≤ Usize.max)
    (reserve : initial.table_depths.length+total ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth ⦃ out =>
      out.1 = .Ok () ∧ LabelCollectionPrefix initial out.2 (count+1) ⦄ := by
  obtain ⟨budget,depths,frame,length,effect⟩ := held
  have used := (effect.counts .branches).2
  have limits := effect.limits
  have room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val := by
    rw [frame]
    simp only [ChargeCounter.used,ite_true] at used
    simp only
    rw [limits]
    omega
  have fits : compiler.table_depths.length < Usize.max := by rw [frame]; simp only; omega
  have request : compiler.table_depths.length+1 ≤ bound := by rw [frame]; simp only; omega
  obtain ⟨⟨reply,after⟩,called,accepted,growth,appended⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state depth room fits request)
  dsimp only at accepted growth appended
  subst reply
  obtain ⟨nextBudget,nextDepths,nextFrame,nextValues⟩ := compiler_table_label_success ops law compiler after state depth called
  have counts : nextDepths.length = initial.table_depths.length+(count+1) := by
    have lengths := congrArg List.length nextValues
    simp only [List.length_append,List.length_singleton] at lengths
    change nextDepths.length = compiler.table_depths.length+1 at lengths
    rw [frame] at lengths
    simp only at lengths
    omega
  have nextEffect : CompilationBudgetEffect initial.budget nextBudget
      (fun counter => if counter = .branches then count+1 else 0) := by
    rw [nextFrame] at growth
    rw [frame] at growth
    exact (effect.trans growth).weaken (by intro counter; cases counter <;> simp)
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),after),called,rfl,nextBudget,nextDepths,?_,counts,nextEffect⟩
  rw [nextFrame,frame]

end Itasca.Compiler

end

/-! ## Source Table Demand -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

private theorem table_suffix_final_observation {data start remaining observations result state}
    (trace : Body.CallbackTrace.TableSuffix data start remaining observations result state) :
    result = .Ok () → ∃ prior action reply,
      observations = prior ++ [⟨.op state action,reply⟩] := by
  induction trace with
  | failed error labels count outcomes => intro impossible; cases impossible
  | complete labels length fallback outcomes =>
    intro _
    exact ⟨_,_,_,rfl⟩

/-- The independently accepted table loop records its final marked state.
A retained source body suffix therefore bounds that state by the independent
whole-body demand, without an accepted compiler callback premise. -/
theorem source_table_loop_demand
    (before after final : List Observation) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (shape : Body.Control.Shape st) (count : U32)
    (reference : code.branch_table_with_loop recorder st data env before count none 0#u32 =
      .ok (.Ok (),out,after))
    (tail : code.body_loop_loop recorder data env ctx index after out = .ok (.Ok (),final)) :
    out.core.vals.length ≤ (observationDemand final).operands ∧
    out.core.ctrls.length ≤ (observationDemand final).controls := by
  obtain ⟨observations,recorded,trace⟩ := Body.CallbackTrace.table_loop_records recorder id recorder_records
    ⟨st⟩ data env shape (by simp) count 0#u32 none (by simp) before (.Ok ()) out after reference
  obtain ⟨suffix,retained⟩ := source_body_recorded_prefix after final out data env ctx index (.Ok ()) tail
  obtain ⟨prior,action,reply,events⟩ := table_suffix_final_observation trace rfl
  apply observationDemand.recorded_op (prior := before ++ prior) (suffix := suffix) (action := action) (reply := reply)
  dsimp only [id] at recorded
  simp only [retained,recorded,events,List.append_assoc,List.singleton_append]

end Itasca.Compiler

end

/-! ## Table Label Collection Replay -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Replay all actual Wasm 2 vector labels with independent scratch and branch
bounds. The remaining final-callback obligation receives the exact decoded
source list, not an arbitrary scratch buffer or an assumed target success. -/
theorem compiler_table_loop_collect_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (count : U32) (all : List U32)
    (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : Body.BrTable.LabelsDecoded data st.pos all out.core.pos)
    (branches : compiler.budget.branches.val+count.val ≤ compiler.budget.limits.max_branch_table_entries.val)
    (capacity : count.val ≤ Usize.max) (reserve : count.val ≤ bound)
    (post : code.BodyState → V → runtime.compiler.FunctionCompiler A → Prop)
    (finish : ∀ (state : code.BodyState) current marked depth ts sourceBefore sourceAfter,
      LabelCollectionPrefix compiler current count.val →
      TableDecodeRead data all out.core.pos count.val state.core current.table_depths.val depth →
      state.core.vals = st.vals → state.core.ctrls = st.ctrls →
      code.mark_unreachable state.core = .ok marked →
      source.on_br_table sourceBefore marked depth ts = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table current marked depth ts
        ⦃ result => result.1 = .Ok () ∧ post {state with core := marked} sourceAfter result.2 ⦄)
    (reference : code.branch_table_with_loop source st data env before count none 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env compiler count none 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        post out after result.2.2 ⦄ := by
  let related := fun index state (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodePrefix data all out.core.pos index state current.table_depths.val ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  let readRelated := fun index state depth (_ : signature.ResultType) (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodeRead data all out.core.pos index state current.table_depths.val depth ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  have readMoves : ∀ (index : U32) (state : code.BodyState) sourceBefore current depth ts next,
      index.val ≤ count.val → related index.val state.core sourceBefore current →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated index.val next.core depth ts sourceBefore current := by
    intro index state sourceBefore current depth ts next bounded held read
    have actual := reader_table_label state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨held.1,held.2.1.read (by omega) read,values.trans held.2.2.1,controls.trans held.2.2.2⟩
  have label : ∀ (index : U32) state sourceBefore current depth ts sourceAfter,
      index.val < count.val → readRelated index.val state depth ts sourceBefore current →
      source.on_br_table_label sourceBefore state depth = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table_label current state depth
        ⦃ result => result.1 = .Ok () ∧ related (index.val+1) state sourceAfter result.2 ⦄ := by
    intro index state sourceBefore current depth ts sourceAfter remaining held _
    obtain ⟨⟨reply,targetAfter⟩,called,accepted,collected⟩ := WP.spec_imp_exists
      (held.1.collect_available ops law bound allocation compiler current state depth index.val count.val
        remaining (by simpa [empty] using branches) (by simpa [empty] using capacity) (by simpa [empty] using reserve))
    dsimp only at accepted collected
    subst reply
    obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law current targetAfter state depth called
    have decodedPrefix := held.2.1.collect
    apply WP.exists_imp_spec
    refine ⟨(.Ok (),targetAfter),called,rfl,collected,?_,held.2.2⟩
    simpa only [frame,appended] using decodedPrefix
  obtain ⟨targetAfter,called,retained⟩ := Body.Visitor.table_loop_reader_accepted_replay source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) related readRelated post data env count
    readMoves label (fun state sourceBefore current marked depth ts sourceAfter held mark call =>
      finish state current marked depth ts sourceBefore sourceAfter held.1 held.2.1 held.2.2.1 held.2.2.2 mark call)
    0#u32 (by simp) none st out before after compiler
    ⟨LabelCollectionPrefix.initial compiler,by simpa [empty] using TableDecodePrefix.initial st decoded,rfl,rfl⟩ reference
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,targetAfter),called,rfl,rfl,retained⟩

end Itasca.Compiler

end

/-! ## Table Source Frame -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent source table loops retain operands and controls until their
single final unreachable transformation. This describes the source reader,
without any compiler-success or target callback assumption. -/
theorem source_table_loop_frame {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (count index : U32)
    (arity : Option Usize)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val)
    (reference : code.branch_table_with_loop source st data env before count arity index =
      .ok (.Ok (),out,after)) :
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok out.core := by
  let related := fun (_ : Nat) (state : code.OpIterState) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let readRelated := fun (_ : Nat) (state : code.OpIterState) (_ : U32) (_ : signature.ResultType) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let post := fun (final : code.BodyState) (_ _ : V) =>
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok final.core
  have readMoves : ∀ (i : U32) (state : code.BodyState) left right depth ts next,
      i.val ≤ count.val → related i.val state.core left right →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated i.val next.core depth ts left right := by
    intro i state left right depth ts next _ held read
    have actual := reader_table_label state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨values.trans held.1,controls.trans held.2.1,held.2.2⟩
  obtain ⟨targetAfter,_,retained⟩ := Body.Visitor.table_loop_reader_accepted_replay source source related readRelated post
    data env count readMoves
    (by
      intro i state left right depth ts next _ held called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,values,controls,rfl⟩)
    (by
      intro state left right marked depth ts next held mark called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,state.core,values,controls,mark⟩)
    index bounded arity st out before after before ⟨rfl,rfl,rfl⟩ reference
  exact retained

/-- Source frame preservation and the independently decoded final cursor fix
the final marked state uniquely, including unreachable operand truncation. -/
theorem source_table_loop_marked {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (count index : U32)
    (arity : Option Usize)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val) (shape : Body.Control.Shape st)
    (reference : code.branch_table_with_loop source st data env before count arity index =
      .ok (.Ok (),out,after))
    (state marked : code.OpIterState) (values : state.vals = st.vals) (controls : state.ctrls = st.ctrls)
    (position : state.pos = out.core.pos) (mark : code.mark_unreachable state = .ok marked) :
    marked = out.core := by
  obtain ⟨last,lastValues,lastControls,lastMark⟩ := source_table_loop_frame source data env count index arity
    st out before after bounded reference
  have lastShape : Body.Control.Shape last :=
    ⟨by simpa only [lastControls] using shape.ordered,
      by simpa only [lastControls,lastValues] using shape.bounded⟩
  have lastSpec := code.mark_unreachable_total last lastShape
  rw [lastMark,WP.spec_ok] at lastSpec
  have sameValues := values.trans lastValues.symm
  have sameControls := controls.trans lastControls.symm
  have samePosition := position.trans lastSpec.2.2.1
  have same : state = last := by
    cases state
    cases last
    simp_all only [code.OpIterState.mk.injEq]
  rw [same,lastMark] at mark
  simpa only [Result.ok.injEq] using mark.symm

end Itasca.Compiler

end

/-! ## Table Loop Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The full actual Wasm 2 table loop accepts an independent source run.
All streamed label callbacks and the final lowering callback are constructed
from source target geometry, exact decoding, and numeric resource bounds. -/
theorem compiler_table_reader_loop_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (count : U32) (all : List U32)
    (shape : Body.Control.Shape st) (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : Body.BrTable.LabelsDecoded data st.pos all out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(count.val+1)+1))
    (branches : compiler.budget.branches.val+(count.val+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : count.val+1 ≤ Usize.max) (scratchReserve : count.val+1 ≤ bound)
    (depthCount : count.val+1 ≤ U32.max)
    (aligned : compiler.reachable = true → SourceAligned compiler)
    (depthsValid : compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length)
    (widths : compiler.reachable = true → ∀ depth ∈ all,
      ∀ (index : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[index.val]? = some frame →
        index.val+depth.val+1 = compiler.frames.val.length → (frameBranchWidth frame).val+1 ≤ compiler.height.val)
    (fixups : compiler.reachable = true → FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.reachable = true → compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (selector : U32)
    (selectorAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector)
    (reference : code.branch_table_with_loop source st data env before count none 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env compiler count none 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0) ⦄ := by
  refine compiler_table_loop_collect_available ops law bound allocation source before after compiler st out data env
     count all empty length decoded (by omega) (by omega) (by omega)
    (fun _ _ targetAfter => CompilationBudgetEffect compiler.budget targetAfter.budget
      (fun counter => match counter with
        | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0)) ?_ reference
  intro state current marked depth ts sourceBefore sourceAfter collected read values controls mark _
  have markedEq := source_table_loop_marked source data env count 0#u32 none st out before after (by simp)
    shape reference state.core marked values controls (read.cursor length) mark
  subst marked
  have whole := read.complete length
  have depthLength := read.length
  obtain ⟨budget,depths,frame,_,effect⟩ := collected
  have unchangedInstructions := effect.uncharged .instructions (by simp)
  change budget.instructions = compiler.budget.instructions at unchangedInstructions
  have sameLimits := effect.limits
  have capacityCurrent : CallbackCapacity current out.core bound (2*(count.val+1)+1) := by
    rw [frame]
    refine ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,capacity.sourceReserve,
      capacity.coordinate,?_,capacity.operands,capacity.slots⟩
    change budget.instructions.val+(2*(count.val+1)+1) ≤ budget.limits.max_instructions.val
    rw [unchangedInstructions,sameLimits]
    exact capacity.instructions
  have branchRoom : current.budget.branches.val < current.budget.limits.max_branch_table_entries.val := by
    have used := (effect.counts .branches).2
    simp only [ChargeCounter.used,ite_true] at used
    rw [frame]
    simp only
    rw [sameLimits]
    omega
  have callback := compiler_on_br_table_available ops law bound allocation current out.core depth ts selector
    (by simpa only [depthLength] using capacityCurrent) branchRoom
    (by change current.table_depths.val.length < Usize.max; omega)
    (by change current.table_depths.val.length+1 ≤ bound; omega)
    (by omega)
    (by simpa only [SourceAligned,frame] using aligned)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using depthsValid (by simpa only [frame] using live) depth member)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using widths (by simpa only [frame] using live) depth member)
    (by simpa only [frame] using fixups)
    (by simpa only [frame] using tables)
    (by simpa only [frame] using selectorAt)
  apply WP.spec_mono callback
  intro result held
  refine ⟨held.1,?_⟩
  have bufferLength : depths.val.length = count.val := by simpa only [frame] using depthLength
  have lowerEffect := held.2
  rw [frame] at lowerEffect
  exact (effect.trans lowerEffect).weaken (by intro counter; cases counter <;> simp [bufferLength])

end Itasca.Compiler

end

/-! ## Reached Table Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Full Wasm 2 table reading accepts from independent source validation,
retained frame/operand geometry, and explicit numeric resource bounds. Both
live and dead tables include every label and the separately decoded fallback. -/
theorem reached_br_table_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (depths : List U32) (fallback : U32)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(depths.length+1)+1))
    (branches : compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : depths.length+1 ≤ Usize.max) (scratchReserve : depths.length+1 ≤ bound)
    (depthCount : depths.length+1 ≤ U32.max)
    (boundary : CompilerTableBoundary compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (reference : code.step_body source st data env ctx index 14#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 14#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(depths.length+1)+1 | .branches => depths.length+1 | _ => 0) ⦄ := by
  rw [Body.CallbackTrace.dispatch_br_table] at reference ⊢
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  obtain ⟨count,first,selectorType,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets source before after st out data env
      _ p.current.ctrl controls p.opened.shape.core reference
  obtain ⟨sourceCount,sourceFirst,last,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all = depths++[fallback] := (allDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  have geometry : ∃ selector : U32,
      (compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) ∧
      (compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length) ∧
      (compiler.reachable = true → ∀ depth ∈ all,
        ∀ (frameIndex : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[frameIndex.val]? = some frame →
          frameIndex.val+depth.val+1 = compiler.frames.val.length →
          (frameBranchWidth frame).val+1 ≤ compiler.height.val) := by
    by_cases live : compiler.reachable = true
    · have encoded : Body.BrTable.Decoded data st.core.pos depths fallback out.core.pos :=
        ⟨count,first,last,countSource,lengthSource,labelsSource,defaultSource⟩
      obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs source p same fronts invariant.entryChain
        (invariant.live live).1 (invariant.known live) (monomorphic live) before after out depths fallback
        out.core.pos encoded reference
      have layout := (invariant.live live).2.layout
      rw [stackEq] at layout
      obtain ⟨selector,selectorAt,_⟩ := layout.condition
      refine ⟨selector,fun _ => selectorAt,?_,?_⟩
      · intro _ depth member
        rw [allEq] at member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨frameIndex,frame,sourceAt,condition,found,position,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        omega
      · intro _ depth member frameIndex frame found position
        rw [allEq] at member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨actualIndex,actualFrame,sourceAt,condition,actualFound,actualPosition,shape,_,_,width,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        have sameIndex : frameIndex = actualIndex := UScalar.eq_of_val_eq (by omega)
        subst actualIndex
        rw [found] at actualFound
        have sameFrame := Option.some.inj actualFound
        subst actualFrame
        calc
          _ = slots scope.branchTypes+1 := congrArg (fun n => n+1) shape.toScopeFrameShape.branch_width
          _ ≤ compiler.height.val := by omega
    · exact ⟨0#u32,(fun impossible => False.elim (live impossible)),
        (fun impossible => False.elim (live impossible)),(fun impossible => False.elim (live impossible))⟩
  obtain ⟨selector,selectorAt,depthsValid,widths⟩ := geometry
  have poppedShape := code.pop_with_type.total {st.core with pos := first} .I32
    (show Body.Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedShape
  have readCount := reader.read_u32_leb.complete data st.core.pos count first countSource
  unfold code.branch_table_with at reference ⊢
  rw [readCount] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  rw [popCall] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  have accepted := compiler_table_reader_loop_available ops law bound allocation source before after compiler popped out
    data env count all poppedShape.1 boundary.depths countEq (by simpa only [popPos] using allDecoded)
    (by simpa only [lengthSource] using capacity) (by simpa only [lengthSource] using branches)
    (by omega) (by omega) (by omega) (fun _ => invariant.sources) depthsValid widths
    (fun _ => fixups) (fun _ => boundary.targets) selector selectorAt reference
  obtain ⟨⟨reply,resultOut,targetAfter⟩,called,ok,sameResult,effect⟩ := WP.spec_imp_exists accepted
  dsimp only at ok sameResult effect
  subst reply resultOut
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,targetAfter),called,rfl,rfl,?_⟩
  exact effect.weaken (by intro counter; cases counter <;> simp [lengthSource])

end Itasca.Compiler

end

/-! ## Source Bound Table Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- A full reached Wasm 2 branch table accepts from source-only demand.
The source reference supplies decoding and stack peaks; consumed bytes pay
all label charges, stubs, reserves, and arithmetic bounds internally. -/
theorem IndexedTableReaderCompilerPoint.table_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (byte : data.val[st.core.pos.val] = 14#u8)
    (reference : code.step_body recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  have raw := canonical
  rw [Body.CallbackTrace.dispatch_br_table] at raw
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := pending.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets recorder before after _ out data env
      _ pending.current.ctrl controls pending.opened.shape.core raw
  obtain ⟨depths,fallback,last,allEq,labelsDecoded,fallbackDecoded⟩ := allDecoded.unsnoc (by
    intro empty
    simp only [empty,List.length_nil] at countEq
    omega)
  have lengthSource : depths.length = count.val := by
    rw [allEq,List.length_append,List.length_singleton] at countEq
    omega
  have encoded : Body.BrTable.Decoded data next depths fallback out.core.pos :=
    ⟨count,first,last,countDecoded,lengthSource,labelsDecoded,fallbackDecoded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32
    (show Body.Control.Shape {st.core with pos := first} from
      ⟨pending.opened.shape.core.ordered,pending.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedSpec
  have readCount := reader.read_u32_leb.complete data next count first countDecoded
  have loopReference : code.branch_table_with_loop recorder popped data env before count none 0#u32 =
      .ok (.Ok (),out,after) := by
    unfold code.branch_table_with at raw
    rw [readCount] at raw
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at raw
    rw [popCall] at raw
    simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] using raw
  have operands := (source_table_loop_demand before after final popped out data env ⟨sourceLocals,ft.results⟩
    index poppedSpec.1 count loopReference tail).1
  have countSpan := countDecoded.span
  change next.val < first.val ∧ first.val ≤ next.val+5 ∧ first.val ≤ data.length at countSpan
  have labelSpan := table_labels_length_span allDecoded
  have endBound := (allDecoded.span countSpan.2.2).2
  have spanPositive : st.core.pos.val < out.core.pos.val := by omega
  have remaining : st.core.pos.val+(out.core.pos.val-st.core.pos.val) ≤ data.length := by omega
  have instructionPaid : 2*(depths.length+1)+1 ≤ 3*(out.core.pos.val-st.core.pos.val) := by omega
  have branchPaid : depths.length+1 ≤ out.core.pos.val-st.core.pos.val := by omega
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor remaining instructionPaid out.core operands
  have branchRoom := budget.room .branches (room.counters .branches) remaining (amount := depths.length+1)
    (by simpa only [bodyResourceRate,Nat.one_mul] using branchPaid)
  change compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val at branchRoom
  have sourceSize := room.pc
  have reserve := room.temporary
  have words : U32.max ≤ Usize.max := by scalar_tac
  have accepted := reached_br_table_available pending ops law bound allocation initial compiler recorder
    before after out ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
    depths fallback encoded capacity branchRoom (by omega) (by omega) (by omega) point.tables ledger.fixups canonical
  rw [byte]
  apply WP.spec_mono accepted
  intro result held
  refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
  intro counter
  cases counter <;> simp only [bodyResourceRate] <;> omega

end Itasca.Compiler

end

end

/-! ## ReachedBranchAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Independently accepted source branching selects the retained compiler
frame and proves its argument width. Allocation and instruction room then
establish actual callback acceptance for every depth and label kind. -/
theorem reached_br_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (capacity : CallbackCapacity compiler out.core bound 2)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (reference : code.step_body source st data env ctx index 12#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 12#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  rw [CallbackTrace.dispatch_br] at reference ⊢
  refine CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 2 else 0)) reference ?_
  rintro ⟨depth,view⟩ read _
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler out.core depth view ⦃ _ ⦄
  by_cases live : compiler.reachable = true
  · obtain ⟨scope,discarded,selected,input⟩ := reader_br_layout p same fronts (invariant.known live)
      (monomorphic live) depth view out read
    obtain ⟨frameIndex,frame,sourceAt,found,position,shape,_,_,width⟩ :=
      invariant.branch_layout live depth.val scope selected discarded input
    have holes := fixups frame (List.mem_of_getElem? found)
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    have widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val ≤ compiler.height.val := by
      calc
        _ = slots scope.branchTypes := shape.toScopeFrameShape.branch_width
        _ ≤ compiler.height.val := by omega
    exact compiler_on_br_available ops law bound available compiler out.core capacity frame frameIndex depth view
      (fun _ => found) (fun _ => position) (fun _ => widthFits)
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)
  · obtain ⟨prior,frame,frames,_,_⟩ := invariant.frames.split
    have member : frame ∈ compiler.frames.val := by rw [frames]; simp
    have holes := fixups frame member
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    exact compiler_on_br_available ops law bound available compiler out.core capacity frame 0#usize depth view
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (fun impossible => False.elim (live impossible))
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)

end Itasca.Compiler

end

/-! ## ReachedConditionalBranchAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Independently accepted conditional source branching selects the retained compiler
frame and proves its argument width. Allocation and instruction room then
establish actual callback acceptance for every depth and label kind. -/
theorem reached_br_if_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (capacity : CallbackCapacity compiler out.core bound 3)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (reference : code.step_body source st data env ctx index 13#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 13#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  rw [CallbackTrace.dispatch_br_if] at reference ⊢
  refine CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 3 else 0)) reference ?_
  rintro ⟨depth,view⟩ read _
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler out.core depth view ⦃ _ ⦄
  by_cases live : compiler.reachable = true
  · obtain ⟨scope,discarded,selected,input,targetStack,_⟩ := reader_br_if_layout p same fronts (invariant.known live)
      (monomorphic live) depth view out read
    obtain ⟨frameIndex,frame,sourceAt,condition,found,position,shape,_,_,width,conditionAt,_⟩ :=
      invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
    have holes := fixups frame (List.mem_of_getElem? found)
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    have widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val+1 ≤ compiler.height.val := by
      calc
        _ = slots scope.branchTypes+1 := congrArg (fun n => n+1) shape.toScopeFrameShape.branch_width
        _ ≤ compiler.height.val := by omega
    exact compiler_on_br_if_available ops law bound available compiler out.core capacity frame frameIndex depth condition view
      (fun _ => found) (fun _ => position) (fun _ => widthFits) (fun _ => conditionAt)
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)
  · obtain ⟨prior,frame,frames,_,_⟩ := invariant.frames.split
    have member : frame ∈ compiler.frames.val := by rw [frames]; simp
    have holes := fixups frame member
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    exact compiler_on_br_if_available ops law bound available compiler out.core capacity frame 0#usize depth 0#u32 view
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)

end Itasca.Compiler

end

/-! ## ReachedElseAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- An independently selected then scope retains its unique unpatched guard.
Its frame shape and entry code justify all three actual else-entry paths. -/
theorem StructuredCompilerPrefix.else_available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (capacity : CallbackCapacity compiler state bound 1)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (sourceBt : blocktype) (condition : U32) (form : current.form = .then_ sourceBt condition)
    (bt : signature.BlockType) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
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
  have holes := fixups frame (by rw [frames]; simp)
  have room := capacity.codeCapacity
  have reserve := capacity.codeReserve
  simp only [alloc.vec.Vec.length] at room reserve
  exact compiler_else_available ops bound available compiler state capacity bt frame prior frames liveGuard owned
    (by change frame.fixups.val.length < Usize.max; omega)
    (by change frame.fixups.val.length+1 ≤ bound; omega)

/-- Independent source else acceptance identifies the active then-scope;
its physical guard and source-paid reserve establish actual compiler acceptance. -/
theorem reached_else_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipper parents current p.parents p.current)
    (capacity : CallbackCapacity compiler out.core bound 1)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (reference : code.step_body source st data env ctx index 5#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 5#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,sourceForm,_⟩ := reader_else p source before after out ctx byte reference
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Body.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  rw [Body.CallbackTrace.dispatch_else] at reference ⊢
  refine Body.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  rintro ⟨kind,bt⟩ _ _
  exact invariant.else_available ops bound available out.core capacity fixups _ condition form bt

end Itasca.Compiler

end

/-! ## ReachedEndAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Retained scope ownership discharges every end-callback patch and map
lookup, including root epilogues, guarded blocks, and dead scopes. -/
theorem StructuredCompilerPrefix.end_available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (capacity : CallbackCapacity compiler state bound 1)
    (coordinate : compiler.function.body_start.val+state.pos.val ≤ Usize.max)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have size := compiler.frames.property
    simp only [frames,List.length_append,List.length_singleton] at size
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have rootNoGuard : frame.kind = .Body → frame.if_pc = none := by
    intro root
    have form : current.form = .body := by
      have same := shape.kind
      cases found : current.form <;> simp_all [ScopeForm.kind]
    have guard := shape.guard
    simpa [form,SourceScope.guardPosition] using guard
  have sites := invariant.mode.sites frame (by rw [frames]; simp)
  exact compiler_end_available ops bound available compiler state capacity frame rest
    (by simpa [rest] using frames) rootNoGuard sites.guard sites.branches.branches shape.mapBound coordinate

/-- Replay the independently accepted Wasm 2 end reader through the complete
callback, retaining its exact source state and instruction allowance. -/
theorem reached_end_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (source : code.OpVisitor V) (before after : V) (st out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (capacity : CallbackCapacity compiler out.core bound 1)
    (coordinate : compiler.function.body_start.val+out.core.pos.val ≤ Usize.max)
    (reference : code.step_body source st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 11#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [Body.CallbackTrace.dispatch_end] at reference ⊢
  refine Body.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  rintro ⟨kind,bt⟩ _ _
  exact invariant.end_available ops bound available out.core capacity coordinate kind bt

end Itasca.Compiler

end

/-! ## ReachedEnterAcceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Independent source validation supplies the captured block signature,
control base, and live condition layout for all three Wasm 2 scope openers.
Dead scope entry requires only the source signature and resource bounds. -/
theorem reached_enter_available {jumpTables : List U32} {data env sourceLocals index st}
    (p : Pending data env sourceLocals index st) (form : Frames.Form) (initialForm : form.Initial)
    {A V : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (demand : CallbackDemand compiler out.core bound) (scope : ScopeDemand compiler out.core bound)
    (pcRoom : compiler.function.code.length+1 ≤ U32.max)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (reference : code.step_body source st data env ctx index form.opcode before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  obtain ⟨bt,ins,outs,remaining,base,_,read,post⟩ := reader_enter p form initialForm source before after out ctx
    byte reference
  obtain ⟨signature,selected,_⟩ := signatures.select post.inputs post.outputs
  have controls := (post.front initialForm).1
  have valuesFit : (Frames.Saved.fresh base form bt ins outs).ctrl.value_stack_base.val ≤ out.core.vals.val.length := by
    exact (post.front initialForm).2.1
  have conditionLayout : compiler.reachable = true → form.kind = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32]) := by
    intro live thenKind
    rcases initialForm with rfl | rfl | rfl
    · cases thenKind
    · cases thenKind
    · obtain ⟨front,_,oldTypes,_⟩ := post.callback_inputs (.inr (.inr rfl)) (monomorphic live)
        (invariant.known live) (invariant.live live).2.layout signatures
      refine ⟨front ++ ins.map Translation.valueType,?_⟩
      have layout := (invariant.live live).2.layout
      simpa [Frames.Form.args,List.append_assoc] using oldTypes ▸ layout
  have callback := compiler_enter_available ops bound available compiler out.core demand scope
    (Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Frames.Saved.ctrl) form.kind bt signature
    controls selected valuesFit pcRoom conditionLayout
  have actual : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (enterAction form bt)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
    rcases initialForm with rfl | rfl | rfl <;> exact callback
  have dispatch : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode compiler =
      CallbackTrace.bodyRun (code.enter_info st data env form.kind)
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler := by
    rcases initialForm with rfl | rfl | rfl
    · exact CallbackTrace.dispatch_block _ _ _ _ _ _ _
    · exact CallbackTrace.dispatch_loop _ _ _ _ _ _ _
    · exact CallbackTrace.dispatch_if _ _ _ _ _ _ _
  rw [dispatch]
  exact CallbackTrace.bodyRun.available_of_read _ _ _ compiler bt out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)) read actual

end Itasca.Compiler

end

end

/-! ## SourceBoundControlAcceptance -/

section

/-!
# Source-bounded control acceptance

Source validation and conservative body bounds construct actual acceptance of metadata-producing control/call readers. The paired resource effect supports the full reached-step theorem.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Source validation and conservative body bounds construct actual acceptance
for every metadata-producing control/call reader. The resource effect is paid
by consumed source bytes; no target-success or callback-demand premise occurs. -/
theorem IndexedTableReaderCompilerPoint.control_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial compiler types functions
      (ft.results.val.map Translation.valueType) localTypes data env sourceLocals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
    (reference : code.step_body recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨capacity,scope,coordinate,progress⟩ := point.control_capacity_from_source before after final out bound room
    budget nonempty next advance inbounds kind byte reference suffix
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have currentMetadata : FunctionParameterSlots compiler env := by
    simpa only [FunctionParameterSlots,state.compiled.metadata.fields.2.1] using metadata
  have currentSignatures : SignatureSequence compiler.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  rw [byte] at reference ⊢
  have liftEffect (allowance : ChargeCounter → Nat) (paid : ∀ counter, allowance counter ≤ bodyResourceRate counter)
      (acceptance : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index kind.opcode compiler
        ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget allowance ⦄) :
      code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index kind.opcode compiler
        ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
          CompilationBudgetEffect compiler.budget result.2.2.budget
            (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
    apply WP.spec_mono acceptance
    intro result held
    refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
    intro counter
    have span : 1 ≤ out.core.pos.val-st.core.pos.val := by omega
    exact (paid counter).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (bodyResourceRate counter) span)
  cases kind with
  | block =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_enter_available pending .block (by simp [Body.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | loop =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_enter_available pending .loop (by simp [Body.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | if_ =>
    apply liftEffect (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_enter_available pending .then_ (by simp [Body.Frames.Form.Initial]) ops bound allocation
      initial compiler recorder before after out ⟨sourceLocals,ft.results⟩ state.compiled state.reach.current
      currentSignatures (capacity.one (by decide)) scope (by have pc := capacity.pc; omega) byte reference
  | else_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_else_available pending ops bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources (capacity.mono (by decide)) ledger.fixups byte reference
  | end_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_end_available ops bound allocation state.compiled recorder before after _ out data env
      ⟨sourceLocals,ft.results⟩ index (capacity.mono (by decide)) coordinate reference
  | br =>
    apply liftEffect (fun counter => if counter = .instructions then 2 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_br_available pending ops law bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
      (capacity.mono (by decide)) ledger.fixups byte reference
  | br_if =>
    apply liftEffect (fun counter => if counter = .instructions then 3 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_br_if_available pending ops law bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
      (capacity.mono (by decide)) ledger.fixups byte reference
  | return_ =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_return_available pending ops bound allocation initial compiler recorder before after out
      ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.reach.current (capacity.one (by decide)) reference
  | call =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_call_available pending ops bound allocation recorder before after compiler out
      ⟨sourceLocals,ft.results⟩ (capacity.one (by decide)) currentMetadata state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) byte reference
  | call_indirect =>
    apply liftEffect (fun counter => if counter = .instructions then 1 else 0)
      (by intro counter; cases counter <;> simp [bodyResourceRate])
    exact reached_indirect_call_available pending ops bound allocation recorder before after compiler out
      ⟨sourceLocals,ft.results⟩ (capacity.one (by decide)) currentSignatures state.compiled.known state.reach.current
      (fun live => (state.compiled.live live).2.layout) ledger.indirect byte reference

end Itasca.Compiler

end
