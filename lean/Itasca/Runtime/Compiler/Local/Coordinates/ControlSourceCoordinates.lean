import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Pair
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Source.SourceEntry
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata

/-!
Sections, each formerly its own module: SourceCoordinateCallbacks, SourceCoordinateTactic, ControlSourceCoordinates.
-/

/-! ## SourceCoordinateCallbacks -/

section

/-!
Source-coordinate order and bounds, with preservation by the compiler primitives. SourceCoordinates is the common certificate used by callback coordinate proofs.
-/

/-! ## Source Coordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Retained source coordinates lie in the declared body interval, are ordered,
and do not exceed the compiler's current source cursor. -/
def SourceCoordinates {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  (∀ coordinate ∈ compiler.function.source_offsets.val.map UScalar.val,
    compiler.function.body_start.val ≤ coordinate ∧ coordinate < compiler.function.body_end.val ∧
      coordinate ≤ compiler.function.body_start.val+compiler.next_source.val) ∧
    (compiler.function.source_offsets.val.map UScalar.val).Pairwise (· ≤ ·)

theorem SourceCoordinates.bounds {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) :
    ∀ coordinate ∈ compiler.function.source_offsets.val.map UScalar.val,
      compiler.function.body_start.val ≤ coordinate ∧ coordinate < compiler.function.body_end.val ∧
        coordinate ≤ compiler.function.body_start.val+compiler.next_source.val := held.1

theorem SourceCoordinates.ordered {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) :
    (compiler.function.source_offsets.val.map UScalar.val).Pairwise (· ≤ ·) := held.2

theorem SourceCoordinates.empty {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (empty : compiler.function.source_offsets.val = []) : SourceCoordinates compiler := by
  constructor <;> simp [empty]

/-- Helpers that retain the coordinate vector and body interval preserve the
invariant whenever the source cursor moves forward. -/
theorem SourceCoordinates.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates before)
    (sources : after.function.source_offsets = before.function.source_offsets)
    (start : after.function.body_start = before.function.body_start)
    (finish : after.function.body_end = before.function.body_end)
    (cursor : before.next_source.val ≤ after.next_source.val) : SourceCoordinates after := by
  constructor
  · intro coordinate member
    rw [sources] at member
    obtain ⟨lower,upper,prior⟩ := held.bounds coordinate member
    rw [start,finish]
    exact ⟨lower,upper,by omega⟩
  · simpa only [sources] using held.ordered

/-- Actual emission appends precisely the current body-relative source origin.
The retained upper bound supplies ordering with every earlier instruction. -/
theorem Emitted.source_coordinates {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    SourceCoordinates after := by
  obtain ⟨budget,code,sources,frame,_,appended⟩ := emitted
  subst after
  constructor
  · intro coordinate member
    change coordinate ∈ sources.val.map UScalar.val at member
    change before.function.body_start.val ≤ coordinate ∧ coordinate < before.function.body_end.val ∧
      coordinate ≤ before.function.body_start.val+before.next_source.val
    rw [appended] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with prior | rfl
    · exact held.bounds coordinate prior
    · exact ⟨by omega,inside,Nat.le_refl _⟩
  · change (sources.val.map UScalar.val).Pairwise (· ≤ ·)
    rw [appended,List.pairwise_append]
    refine ⟨held.ordered,by simp,?_⟩
    intro earlier member later last
    simp only [List.mem_singleton] at last
    subst later
    exact (held.bounds earlier member).2.2

/-- Indexed form consumed by the real publication check, including the
previous-coordinate comparison at every nonzero instruction index. -/
theorem SourceCoordinates.checker {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates compiler) (index : Nat) (bound : index < compiler.function.source_offsets.length) :
    compiler.function.body_start.val ≤ compiler.function.source_offsets.val[index].val ∧
    compiler.function.source_offsets.val[index].val < compiler.function.body_end.val ∧
    (0 < index →
      (compiler.function.source_offsets.val[index-1]'(by
        have bounded : index < compiler.function.source_offsets.val.length := bound
        omega)).val ≤ compiler.function.source_offsets.val[index].val) := by
  have bounded : index < compiler.function.source_offsets.val.length := bound
  have member : compiler.function.source_offsets.val[index].val ∈
      compiler.function.source_offsets.val.map UScalar.val :=
    List.mem_map.mpr ⟨_,List.getElem_mem bounded,rfl⟩
  obtain ⟨lower,upper,_⟩ := held.bounds _ member
  refine ⟨lower,upper,?_⟩
  intro positive
  have order := List.pairwise_iff_getElem.mp held.ordered
  have previousBound : index-1 < (compiler.function.source_offsets.val.map UScalar.val).length := by
    simp only [List.length_map]
    omega
  have currentBound : index < (compiler.function.source_offsets.val.map UScalar.val).length := by
    simpa only [List.length_map] using bounded
  simpa only [List.getElem_map] using order (index-1) index previousBound currentBound (by omega)

end Itasca.Runtime.Compiler

end

/-! ## Source Coordinate Callbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Function setup establishes the empty coordinate invariant before reading
any opcode, directly from actual construction and the start-frame theorem. -/
theorem compiler_start_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (first last : Usize)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex first last = .ok (.Ok (),started)) : SourceCoordinates started := by
  have frame := compiler_function_start_source_frame ops law initial started ctx typeIndex first last (.Ok ()) begun
  have sources := congrArg (fun fields => fields.2.1) frame
  change started.function.source_offsets = initial.function.source_offsets at sources
  apply SourceCoordinates.empty
  rw [sources]
  simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
  subst initial
  rfl

/-- A successful actual emission preserves ordered source coordinates from
its prior cursor bound. Vector and coordinate arithmetic bounds follow from
the successful push and the declared source interval. -/
theorem compiler_emit_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  have codeLength := compiler_emit_code_success ops law before after instruction called
  have codeSize := congrArg List.length codeLength
  simp only [List.length_append,List.length_singleton] at codeSize
  have sourceLength := compiler_emit_source_length_success ops law before after instruction called
  have codeBound := after.function.code.property
  have sourceBound := after.function.source_offsets.property
  have endBound : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have emitted := compiler_emit ops law before instruction (by omega) (by omega) (by omega)
  rw [called,WP.spec_ok] at emitted
  exact (emitted rfl).source_coordinates held inside

/-- Elided copies retain the vector; emitted copies append the current source
origin just like any other actual instruction. -/
theorem compiler_copy_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  rcases runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count (.Ok ()) called with
    ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · subst after
    exact held
  · exact compiler_emit_source_coordinates ops law before after _ held inside emitted

/-- Successful observation advances the cursor while preserving the stored
source vector and body interval. -/
theorem compiler_observe_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : SourceCoordinates before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  change ObserveFrame before after at frame
  have cursor := compiler_observe_cursor ops law before after state (.Ok ()) called rfl
  apply held.advance
  · rw [frame]
  · rw [frame]
  · rw [frame]
  · rw [cursor]
    exact forward

/-- Ordinary emission/observation is one complete source-coordinate step. -/
theorem compiler_finish_op_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) called).success
  have coordinates := compiler_emit_source_coordinates ops law before middle instruction held inside emitted
  have cursor := compiler_emit_cursor ops before middle instruction (.Ok ()) emitted
  exact compiler_observe_source_coordinates ops law middle after state coordinates (by simpa only [cursor] using forward) rest

/-- Metadata-preserving helpers with unchanged coordinates and cursor cannot
invalidate source publication bounds. -/
theorem SourceCoordinates.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : SourceCoordinates before) (stable : CompilerStable before after)
    (sources : after.function.source_offsets = before.function.source_offsets)
    (cursor : after.next_source = before.next_source) : SourceCoordinates after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  exact held.advance sources start finish (by rw [cursor])

theorem compiler_patch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status,after))
    (held : SourceCoordinates before) :
    SourceCoordinates after :=
  held.retained (compiler_patch_ordinary_result ops before after pc target status called).stable
    (compiler_patch_sources_unchanged ops before after pc target status called)
    (compiler_patch_cursor ops before after pc target status called)

theorem compiler_pc_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (status,after))
    (held : SourceCoordinates before) : SourceCoordinates after := by
  have effect := compiler_pc ops before
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,_,budget,same⟩ := effect
  change after = {before with budget} at same
  subst after
  exact held

theorem compiler_fixups_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output)
    (held : SourceCoordinates before) : SourceCoordinates (snapshotCompiler output) :=
  held.retained (compiler_fixups_ordinary_result ops before sites target index status output called).stable
    (compiler_fixups_sources_unchanged ops before sites target index status output called)
    (compiler_fixups_cursor ops before sites target index status output called)

theorem compiler_fixups_after_if_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output)
    (held : SourceCoordinates before) : SourceCoordinates (snapshotCompiler output) :=
  compiler_fixups_source_coordinates ops before sites target index status output called held

theorem compiler_pair_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after))
    (held : SourceCoordinates before) :
    SourceCoordinates after := by
  have frame := (runtime.compiler.FunctionCompiler.pair.inv ops before after a b status accepted).1
  change after = _ at frame
  rw [frame]
  exact held

/-- Conditional forms allow composition through extracted result matches. -/
theorem compiler_emit_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status,after))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_emit_source_coordinates ops law before after instruction held inside called

theorem compiler_observe_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status,after))
    (held : SourceCoordinates before) (forward : before.next_source.val ≤ state.pos.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_observe_source_coordinates ops law before after state held forward called

theorem compiler_copy_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status,after))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_copy_source_coordinates ops law before after dst src count held inside called

theorem compiler_finish_op_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status,after))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_finish_op_source_coordinates ops law before after state instruction held inside forward called

end Itasca.Runtime.Compiler

end

end

/-! ## SourceCoordinateTactic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

macro "coordinates_close" : tactic => `(tactic|
  (first | assumption | (simp_all [SourceCoordinates,compilerOrdinaryMetadata,compilerMetadata,
    snapshotCompiler,Prod.mk.injEq,source_unit_eq]; try omega)))

/- Reduce only the outer parser match. Traversing every inactive branch of
an extracted opcode dispatcher is both unnecessary and expensive. The local
declaration change is checked for definitional equality. -/
open Lean Meta Elab Tactic in
elab "coordinates_head " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, rhs) := ty.eq? | throwError "not an equation"
  let reduced ← whnfCore lhs
  if reduced == lhs then throwError "already in head normal form"
  let next ← (← getMainGoal).changeLocalDecl hyp.fvarId! (← mkEq reduced rhs)
  replaceMainGoal [next]

open Lean Meta Elab Tactic in
elab "coordinates_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have coordinates := compiler_observe_source_coordinates_result $ops $law _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have coordinates := compiler_emit_source_coordinates_result $ops $law _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have coordinates := compiler_copy_source_coordinates_result $ops $law _ _ _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have coordinates := compiler_finish_op_source_coordinates_result $ops $law _ _ _ _ _
        $h (by coordinates_close) (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have coordinates := compiler_pair_source_coordinates $ops _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.pc =>
      `(tactic| have coordinates := compiler_pc_source_coordinates $ops _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.control.FunctionCompiler.patch =>
      `(tactic| have coordinates := compiler_patch_source_coordinates $ops _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 =>
      `(tactic| have coordinates := compiler_fixups_source_coordinates $ops _ _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 =>
      `(tactic| have coordinates := compiler_fixups_after_if_source_coordinates $ops _ _ _ _ _ _ $h (by coordinates_close))
    | _ => throwError "not a compiler helper"
  evalTactic tac
  evalTactic (← `(tactic| try metadata_effect $h using $ops, $law))
  evalTactic (← `(tactic| try cursor_effect $h using $ops, $law))

macro "coordinates_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; coordinates_close)
  | coordinates_head $h
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (coordinates_effect $h using $ops, $law; coordinates_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; coordinates_close)
  | (fail_if_no_progress simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,bind_ok,bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value,called,rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue,secondValue⟩)
     | skip
     try coordinates_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

end Itasca.Runtime.Compiler

end

/-! ## ControlSourceCoordinates -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Opening a structured frame emits only at the current source origin. -/
theorem compiler_enter_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) called).2.2 rfl
  have publication := publish law
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have frame := publication.frame
  change middle = _ at frame
  have sourceLengths := publication.sources
  have start : middle.function.body_start = before.function.body_start := by rw [frame]
  have finish : middle.function.body_end = before.function.body_end := by rw [frame]
  have cursor : middle.next_source = before.next_source := by rw [frame]
  have middleHeld : SourceCoordinates middle := by
    unfold SourceCoordinates at held ⊢
    rw [start, finish, cursor, sourceLengths]
    cases reach : before.reachable <;> cases kind <;>
      simp only [enterPrefix, List.map_nil, List.map_cons, List.append_nil] <;>
      first
      | exact held
      | (constructor
         · intro coordinate member
           rcases List.mem_append.mp member with old | fresh
           · exact held.1 coordinate old
           · simp only [List.mem_singleton] at fresh
             subst coordinate
             exact ⟨by omega, inside, Nat.le_refl _⟩
         · rw [List.pairwise_append]
           refine ⟨held.2, by simp only [List.pairwise_singleton], ?_⟩
           intro earlier old later fresh
           simp only [List.mem_singleton] at fresh
           subst later
           exact (held.1 earlier old).2.2)
  have effect := compiler_observe ops law middle state
  rw [observed, WP.spec_ok] at effect
  have position : after.next_source = state.pos := (effect rfl).2.2.2.2.2.2.2.2.1
  unfold SourceCoordinates at middleHeld ⊢
  rw [observedFrame]
  constructor
  · intro coordinate member
    obtain ⟨lower, upper, prior⟩ := middleHeld.1 coordinate member
    refine ⟨lower, upper, ?_⟩
    change coordinate ≤ middle.function.body_start.val + after.next_source.val
    rw [position]
    rw [cursor] at prior
    omega
  · exact middleHeld.2


/-- Branch stubs, copies, and patching retain source-coordinate order. -/
theorem compiler_branch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch,Bool.false_eq_true,ite_false,ite_true] at called <;>
    repeat' coordinates_step called using ops, law

/-- Closing source scopes patches control targets and emits the root return
at the same source origin as every other instruction in the callback. -/
theorem compiler_end_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at called
  repeat' coordinates_step called using ops, law

/-- Else-arm jumps and their patched destinations retain coordinate order. -/
theorem compiler_else_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at called
  repeat' coordinates_step called using ops, law

end Itasca.Runtime.Compiler

end
