import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Local.Demand.IndependentBodyDemand
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Checking.LoopBranchInstructionPrefix
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixOpenDormant
import Itasca.Runtime.Compiler.Local.Source.StartJumpTableBounds
import Itasca.Runtime.Compiler.Local.Checking.TableCallbackInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedReturnAcceptance
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.StructuredRootMapPublication
import Itasca.Runtime.Compiler.Local.Checking.FunctionStartExitSlots
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Body.Reader.Control.RootCompilation
import Itasca.Runtime.Compiler.Body.Reader.Calls.InstructionPrefix
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarTargetEffects
import Itasca.Runtime.Compiler.Local.Publication.TableMapPublication
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects

/-!
Sections, each formerly its own module: SourceControlCapacity, TerminalInstructionPrefix, BranchTableSourceTransferBounds, BranchTableInstructionPrefixWasm2, EnterInstructionPrefixWasm2, RootInstructionPrefix, ControlCheckedPrefixWasm2, ClosedInstructionPrefix, BranchTablePublication.
-/

/-! ## SourceControlCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent control-reader success and its retained source suffix supply
all instruction, control, operand, reserve, slot, and end-coordinate demands.
No compiler callback success or caller-supplied capacity record is needed. -/
theorem IndexedTableReaderCompilerPointWasm2.control_capacity_from_source {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState) (bound : Nat)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
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
  obtain ⟨value,_,called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ canonical
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

end Itasca.Runtime.Compiler

end

/-! ## TerminalInstructionPrefix -/

section

/-!
Actual source RETURN checks its full result suffix and retains recorded exits.

Main declarations: `reader_return_open_instructions_wasm2` and `reader_unreachable_open_instructions_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.ScalarInstructionPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual source RETURN checks its full result suffix and retains recorded exits. -/
theorem reader_return_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions (p.ft.results.val.map Translate.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  refine ⟨?_,(compiler_return_ordinary_result ops law before after out.core (.Ok ()) callback).exit_slots exits⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm2 p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve, p.signature]) vals (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
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
theorem reader_unreachable_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm2 p
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

end Itasca.Runtime.Compiler

end

/-! ## BranchTableSourceTransferBounds -/

section

/-!
Source typing of every table label supplies overlap-safe transfer bounds and already opened loop targets, including repeated and outer labels.

Main declarations: `StructuredCompilerPrefix.table_transfer_geometry`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableInstructionPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source typing of every table label supplies overlap-safe transfer bounds
and already opened loop targets, including repeated and outer labels. -/
theorem StructuredCompilerPrefix.table_transfer_geometry
    {jumpTables : List U32} {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position stack} {depths : List U32}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current raw position)
    (live : compiler.reachable = true)
    (input : Sequence.stackTypes raw = stack++[.I32])
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

end Itasca.Runtime.Compiler

end

/-! ## BranchTableInstructionPrefixWasm2 -/

section

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
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
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
      st data env before = .ok (.Ok (),final,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,view,last,readState,budget,buffer,
      countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,countEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
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

end

/-! ## EnterInstructionPrefixWasm2 -/

section

/-!
Structured compiler scope-entry checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Entry Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Reader Enter Instruction Prefix Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve instruction
checks from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_open_instructions_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (held : CompilerInstructionPrefix before)
    (form : Wasm2.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter_wasm2 p form initialForm
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
      rcases initialForm with rfl | rfl | rfl <;> simp_all [Wasm2.Frames.Form.kind]
    have layout := (invariant.live live).2.layout
    obtain ⟨front,_,oldTypes,_,_,_,_,_,_,_,_⟩ := post.callback_inputs initialForm
      (reach.current live) (invariant.known live) layout signatures
    refine ⟨front ++ ins.map Translate.valueType,?_⟩
    simpa only [oldTypes,formThen,Wasm2.Frames.Form.args,List.append_assoc] using layout
  apply structured_scope_entry_open_instructions ops law invariant sourceBound out.core
    (Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout held called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Wasm2.Frames.Form.kind]

end Itasca.Runtime.Compiler

end

end

/-! ## RootInstructionPrefix -/

section

/-!
Structured compiler root closure checked instructions and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Root Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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
    (normal : before.reachable = true → Sequence.stackTypes raw = returns)
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

end Itasca.Runtime.Compiler

end

/-! ## Reader Root Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual root END checks every stored instruction from its typed preceding stack and retained exits. -/
theorem StructuredReaderCompilerStateWasm2.root_checked_instructions {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals
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
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm2_spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Wasm2.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Wasm2.outputs, Wasm2.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Sequence.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Wasm2.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translate.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = ft.results.val.map Translate.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Sequence.Realizes false savedCurrent.vals (savedCurrent.outs.map Translate.valueType) := by
      simpa [p, ReaderBoundaryWasm2.pending, mono] using realizes
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

end Itasca.Runtime.Compiler

end

end

/-! ## ControlCheckedPrefixWasm2 -/

section

/-!
All control-reader forms preserve instruction and exit-slot checking at an actual Wasm 2 source boundary. Root END additionally checks the completed code before the final compiler publication check is called.

Main declarations: `StructuredReaderCompilerStateWasm2.control_checked_prefix`. A direct consumer is `Compiler.Body.Reader.Checking.CheckedPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- All control-reader forms preserve instruction and exit-slot checking at
an actual Wasm 2 source boundary. Root END additionally checks the completed
code before the final compiler publication check is called. -/
theorem StructuredReaderCompilerStateWasm2.control_checked_prefix
    {jumpTables : List U32} {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions
      (ft.results.val.map Translate.valueType) locals data env sourceLocals index ft st
      parents current savedParents savedCurrent)
    (ctx : code.Context) (contextSource : ctx.locals = sourceLocals) (C : context)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
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
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
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
    refine ⟨reader_enter_open_instructions_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .block (.inl rfl) ?_ ?_,
      reader_enter_exit_slots_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .block (.inl rfl) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using accepted
  | loop =>
    refine ⟨reader_enter_open_instructions_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .loop (.inr (.inl rfl)) ?_ ?_,
      reader_enter_exit_slots_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .loop (.inr (.inl rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using accepted
  | if_ =>
    refine ⟨reader_enter_open_instructions_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures held .then_ (.inr (.inr rfl)) ?_ ?_,
      reader_enter_exit_slots_wasm2 p ops law initial before after out ctx types functions _ locals parents current
        state.compiled state.reach signatures exits .then_ (.inr (.inr rfl)) ?_ ?_⟩
    all_goals first
      | simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using byte
      | simpa only [ControlReaderKind.opcode,Wasm2.Frames.Form.opcode] using accepted
  | else_ =>
    exact ⟨reader_else_open_instructions_wasm2 p ops law initial before after out ctx state.compiled state.sources held byte accepted,
      reader_else_exit_slots_wasm2 p ops law initial before after out ctx state.compiled state.sources state.fronts state.reach.current exits byte accepted⟩
  | br =>
    exact ⟨reader_br_open_instructions_wasm2 p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound fixups coordinate held (by simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_exit_slots_wasm2 p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current exits (by simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | br_if =>
    exact ⟨reader_br_if_open_instructions_wasm2 p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound held (by simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted),
      reader_br_if_exit_slots_wasm2 p ops law initial before after out ctx state.compiled state.sources state.fronts
        state.reach.current positionBound exits (by simpa only [p,ReaderBoundaryWasm2.pending,ControlReaderKind.opcode,global_simps] using byte) (by simpa only [ControlReaderKind.opcode,global_simps] using accepted)⟩
  | return_ =>
    exact reader_return_open_instructions_wasm2 p ops law initial before after out ctx state.compiled state.sources
      state.reach.current sourceBound bodyBound held exits byte accepted
  | call =>
    exact reader_call_checked_prefix_wasm2 p ops law initial before after out ctx state.compiled metadata
      state.reach.current sourceBound bodyBound held exits byte accepted
  | call_indirect =>
    exact reader_indirect_call_checked_prefix_wasm2 p ops law initial before after out ctx state.compiled C matched contextLocals signatures
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
      exact ⟨reader_nested_end_open_instructions_wasm2 p ops law initial before after out ctx types functions _ locals parents current
          state.compiled nonRoot maps held bodyExtent byte accepted,
        reader_nested_end_exit_slots_wasm2 p ops law initial before after out ctx types functions _ locals parents current
          state.compiled nonRoot maps exits bodyExtent byte accepted⟩

end Itasca.Runtime.Compiler

end

/-! ## ClosedInstructionPrefix -/

section

/-!
Closing the actual reader control stack publishes checks for every stored instruction.

Main declarations: `StructuredReaderCompilerStateWasm2.closed_checked_instructions`. A direct consumer is `Compiler.Body.Reader.Checking.SourceCheckedStepsWasm2`.
-/

namespace Itasca.Runtime.Compiler
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
      {core := {st.core with pos := next}} data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
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

end Itasca.Runtime.Compiler

end

/-! ## BranchTablePublication -/

section

/-!
Actual Wasm 2 table decoding, selector handling and label collection retain publication bounds before its final table callback.

Main declarations: `reader_table_publication_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.JumpTargets`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual Wasm 2 table decoding, selector handling and label collection retain
publication bounds before its final table callback. -/
theorem reader_table_publication_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
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

end Itasca.Runtime.Compiler

end
