import Itasca.Runtime.Compiler.Body.Relations.Calls.ControlCallbackReady
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchEntry
import Itasca.Runtime.Compiler.Body.Relations.Table.BranchTableTables
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Wasm2.Trace.Acceptance
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.ReturnAvailability
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish

/-!
Sections, each formerly its own module: ControlSafetyWasm2, BranchTableLedger, ControlLedger, BranchTableDecodePrefix, ReachedReturnAcceptance.
-/

/-! ## ControlSafetyWasm2 -/

section

/-!
Normal return of structured control reader dispatch.

Main declarations: `StructuredReaderCompilerStateWasm2.control_total`. A direct consumer is `Compiler.Body.Reader.Replay.ReachedSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

theorem StructuredReaderCompilerStateWasm2.control_total {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial compiler types functions returns locals
      data env sourceLocals index ft st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (ctx : code.Context) (opcode : U8) (covered : opcode.val ∈ [2,3,4,5,11,12,13,15])
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with core := {st.core with pos := next}} data env ctx index opcode compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  let pending := state.boundary.pending next advance inbounds
  have ready := state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound
  have bounded : st.core.pos.val ≤ limits.MAX_MODULE_BYTES.val :=
    (by omega : st.core.pos.val ≤ data.length).trans state.boundary.source_bound
  have frameCount : compiler.frames.val.length = st.blocks.val.length := by
    simpa using state.frames_length
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_block]
    exact compiler_enter_reader_total ops law compiler pending .block (.inl rfl) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_loop]
    exact compiler_enter_reader_total ops law compiler pending .loop (.inr (.inl rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_if]
    exact compiler_enter_reader_total ops law compiler pending .then_ (.inr (.inr rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 5#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_else]
    exact state.compiled.close_reader_total ops law bounded _ env true
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 11#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_end]
    exact state.compiled.close_reader_total ops law bounded _ env false
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br]
    exact compiler_branch_reader_total ops law compiler _ data env false pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br_if]
    exact compiler_branch_reader_total ops law compiler _ data env true pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 15#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_return]
    exact compiler_return_reader_wasm2_total ops law compiler _ env index pending.opened.shape.core
      (fun _ => ready.nonempty) (by have := ready.code; omega) (by have := ready.sources; omega) ready.emittedCoordinate
end Itasca.Runtime.Compiler

end

/-! ## BranchTableLedger -/

section

/-!
Auxiliary allocation accounting for br_table compilation.

Main declarations: `compiler_br_table_auxiliary_growth` and `reader_table_ledger_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ControlLedger`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_br_table_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (fallback : U32) (types : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : AuxiliaryGrowth before after := by
  obtain ⟨targets,tables⟩ := compiler_br_table_tables ops law before after state fallback types accepted
  have counts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil,Prod.mk.injEq] at counts
  have growth : before.function.code.val.length ≤ after.function.code.val.length := by
    by_cases live : before.reachable = true
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bound⟩ :=
        compiler_br_table_production ops law before after state fallback types live accepted
      omega
    · obtain ⟨_,code,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types
        (Bool.eq_false_iff.mpr live) accepted
      simp [code]
  unfold AuxiliaryGrowth
  omega

theorem reader_table_ledger_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 14#u8 before = .ok (.Ok (),final,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨_,_,_,_,_,fallback,types,_,_,allocation,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  exact ⟨compiler_br_table_auxiliary_growth ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types callback,
    compiler_br_table_fixup_budget ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types budget callback⟩
end Itasca.Runtime.Compiler

end

/-! ## ControlLedger -/

section

/-!
Allocation accounting for control reader steps.

Main declarations: `reader_control_ledger_wasm2`. A direct consumer is `Compiler.Body.Relations.Replay.ReachedCompilerLedger`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_control_ledger_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (opcode : U8)
    (covered : opcode.val ∈ [2,3,4,5,11,12,13,14,15])
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h
  · obtain rfl : opcode = 2#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 3#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 4#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 5#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 11#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 12#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 13#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 14#u8 := UScalar.eq_of_val_eq h
    exact reader_table_ledger_wasm2 ops law before after st out data env ctx index budget (by simpa only [global_simps] using accepted)
  · obtain rfl : opcode = 15#u8 := UScalar.eq_of_val_eq h
    have effects := reader_return_effects_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableDecodePrefix -/

section

/-!
Independently decoded table labels remaining at a reader boundary. The scratch labels are an exact prefix of the source list, indexed by callbacks.

Main declarations: `TableDecodePrefix` and `TableDecodeRead`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableInstructionPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independently decoded table labels remaining at a reader boundary. The
scratch labels are an exact prefix of the source list, indexed by callbacks. -/
structure TableDecodePrefix (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ tail ∧ BrTable.LabelsDecoded data state.pos tail finish

/-- A label has been read but its callback has not yet appended it. Keeping
its value in the relation prevents arbitrary event arguments from replacing
source-decoded targets. -/
structure TableDecodeRead (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) (depth : U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ depth :: tail ∧ BrTable.LabelsDecoded data state.pos tail finish

/-- Each independently decoded label consumes at least one source byte. -/
theorem table_labels_length_span {data start depths finish}
    (decoded : BrTable.LabelsDecoded data start depths finish) :
    start.val + depths.length ≤ finish.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have span := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem TableDecodePrefix.initial {data all finish} (state : code.OpIterState)
    (decoded : BrTable.LabelsDecoded data state.pos all finish) :
    TableDecodePrefix data all finish 0 state [] := by
  exact ⟨rfl,all,by simp,decoded⟩

/-- The actual successful reader fixes both the next target and byte cursor
by uniqueness of independent unsigned LEB128 decoding. -/
theorem TableDecodePrefix.read {data all finish index depths depth ts out} {state : code.BodyState}
    (held : TableDecodePrefix data all finish index state.core depths)
    (remaining : index < all.length)
    (read : code.read_label_info state data = .ok (.Ok (depth,ts),out)) :
    TableDecodeRead data all finish index out.core depths depth := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  cases tail with
  | nil =>
    have length := congrArg List.length whole
    simp only [List.length_append,List.length_nil,Nat.add_zero] at length
    have prefixLength := held.length
    omega
  | cons first tail =>
    obtain ⟨middle,head,rest⟩ := BrTable.LabelsDecoded.cons_iff.mp decoded
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨_,_,bytes,_⟩ := actual depth ts rfl
    dsimp only at bytes
    obtain ⟨rfl,position⟩ := bytes.unique head
    exact ⟨held.length,tail,whole,by simpa only [position] using rest⟩

/-- The successful callback appends exactly the depth just read. -/
theorem TableDecodeRead.collect {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth) :
    TableDecodePrefix data all finish (index+1) state (depths++[depth]) := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  refine ⟨by simp [held.length],tail,?_,decoded⟩
  simpa [List.append_assoc] using whole

/-- At the separately decoded fallback, all remaining targets have been
accounted for. The vector labels followed by this fallback are exactly the
independent source target list. -/
theorem TableDecodeRead.complete {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : all = depths++[depth] := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail.length = 0 := by omega
  simpa only [List.length_eq_zero_iff.mp empty] using whole

/-- After reading the separately encoded fallback, the cursor is the source
end of the entire table immediate. -/
theorem TableDecodeRead.cursor {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : state.pos = finish := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
  subst tail
  exact (decoded.unique .nil rfl).2.symm

end Itasca.Runtime.Compiler

end

/-! ## ReachedReturnAcceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source return typing and the retained root frame discharge the actual
return callback's width check, including multi-value and vector results. -/
theorem reached_profile_return_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions (p.ft.results.val.map Translate.valueType) locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out.core bound)
    (reference : code.step_profile source st data env ctx index 15#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 15#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨frame,found,resultWidth⟩ := reader_root_frame_wasm2 p compiler invariant.frames same
  rw [Wasm2.CallbackTrace.dispatch_return] at reference ⊢
  refine Wasm2.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value read _
  cases value
  have height : compiler.reachable = true → frame.results.val ≤ compiler.height.val := by
    intro live
    obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
    obtain ⟨front,input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve,p.signature]) values (by simpa [Control.base,controls] using base)
      (invariant.known live) (by simpa [Control.polymorphic,controls] using monomorphic live) read
    have layout := (invariant.live live).2.layout
    rw [input] at layout
    rw [resultWidth,layout.height,slots_append]
    omega
  exact compiler_return_available ops bound available compiler out.core demand frame (fun _ => found) height

end Itasca.Runtime.Compiler

end
