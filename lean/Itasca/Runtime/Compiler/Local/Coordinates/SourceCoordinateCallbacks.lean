import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Source.SourceStartFrame

/-!
Source-coordinate order and bounds, with preservation by the compiler primitives. SourceCoordinates is the common certificate used by callback coordinate proofs.
-/

/-! ## Source Coordinates -/

section

namespace Itasca.Runtime.Code
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
theorem Emitted.sourceCoordinates {A : Type} {before after : runtime.compiler.FunctionCompiler A}
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

end Itasca.Runtime.Code

end

/-! ## Source Coordinate Callbacks -/

section

namespace Itasca.Runtime.Code
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
  exact (emitted rfl).sourceCoordinates held inside

/-- Elided copies retain the vector; emitted copies append the current source
origin just like any other actual instruction. -/
theorem compiler_copy_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.copy at called
  split at called
  · have same := (Prod.mk.inj (Result.ok.injEq.mp called)).2
    subst after
    exact held
  · split at called
    · have same := (Prod.mk.inj (Result.ok.injEq.mp called)).2
      subst after
      exact held
    · obtain ⟨instruction,_,emitted⟩ := bind_ok_inv _ _ _ called
      exact compiler_emit_source_coordinates ops law before after instruction held inside emitted

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
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at called
  obtain ⟨⟨reply,middle⟩,emitted,rest⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ called
  cases reply with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
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
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact held
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, pairs⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        exact held
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
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

end Itasca.Runtime.Code

end
