import Itasca.Runtime.Compiler.Local.Relations.Control
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-! Control-flow effects of entering an else arm. The staged relation retains
normal rejections and the state published before each fallible helper. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- The updated final frame is published even when its fixup reserve rejects. -/
def elsePrepared {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame)
    (budget : runtime.compiler.Budget A) (fixups : alloc.vec.Vec Usize) : runtime.compiler.FunctionCompiler A :=
  {before with budget, reachable := frame.entry_reachable, frames := restore {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups}}

/-- The optional guard patch and final observation, including both early errors. -/
inductive ElseFinish {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState) :
    Option Usize → runtime.compiler.FunctionCompiler A →
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | unguarded {before status after}
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      ElseFinish ops state none before status after
  | pcRejected {guard before error after}
      (counted : runtime.compiler.FunctionCompiler.pc ops before = .ok (.Err error, after)) :
      ElseFinish ops state (some guard) before (.Err error) after
  | patchRejected {guard before target counted error after}
      (count : runtime.compiler.FunctionCompiler.pc ops before = .ok (.Ok target, counted))
      (patched : runtime.compiler.control.FunctionCompiler.patch ops counted guard target = .ok (.Err error, after)) :
      ElseFinish ops state (some guard) before (.Err error) after
  | guarded {guard before target counted patched status after}
      (count : runtime.compiler.FunctionCompiler.pc ops before = .ok (.Ok target, counted))
      (patch : runtime.compiler.control.FunctionCompiler.patch ops counted guard target = .ok (.Ok (), patched))
      (observed : runtime.compiler.FunctionCompiler.observe ops patched state = .ok (status, after)) :
      ElseFinish ops state (some guard) before status after

/-- The live arm first reserves a fixup, publishes the frame, then emits its jump.
A dead arm publishes the frame without either allocation. -/
inductive ElsePrefix {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (before : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (finished : ElseFinish ops state frame.if_pc
        (elsePrepared before frame restore before.budget frame.fixups) status after) :
      ElsePrefix ops state before frame restore status after
  | reserveRejected {error budget fixups} (live : before.reachable = true)
      (reserved : runtime.compiler.Budget.push ops before.budget frame.fixups (alloc.vec.Vec.len before.function.code) =
        .ok (.Err error, budget, fixups)) :
      ElsePrefix ops state before frame restore (.Err error) (elsePrepared before frame restore budget fixups)
  | emitRejected {error budget fixups after} (live : before.reachable = true)
      (reserved : runtime.compiler.Budget.push ops before.budget frame.fixups (alloc.vec.Vec.len before.function.code) =
        .ok (.Ok (), budget, fixups))
      (emitted : runtime.compiler.FunctionCompiler.emit ops (elsePrepared before frame restore budget fixups)
        (.Jump core.num.U32.MAX) = .ok (.Err error, after)) :
      ElsePrefix ops state before frame restore (.Err error) after
  | emitted {budget fixups middle status after} (live : before.reachable = true)
      (reserved : runtime.compiler.Budget.push ops before.budget frame.fixups (alloc.vec.Vec.len before.function.code) =
        .ok (.Ok (), budget, fixups))
      (emit : runtime.compiler.FunctionCompiler.emit ops (elsePrepared before frame restore budget fixups)
        (.Jump core.num.U32.MAX) = .ok (.Ok (), middle))
      (finished : ElseFinish ops state frame.if_pc middle status after) :
      ElsePrefix ops state before frame restore status after

/-- Exact source of a normal callback return. The index/read witnesses retain
which frame and replacement function were actually selected. -/
inductive ElseEffect {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (before : runtime.compiler.FunctionCompiler A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | empty (empty : before.frames.val.isEmpty = true) :
      ElseEffect ops state before (.Err Itasca.error.VisitError.OutOfMemory) before
  | selected {index frame restore status after} (nonempty : before.frames.val.isEmpty = false)
      (subtracted : (alloc.vec.Vec.len before.frames - 1#usize : Result Usize) = .ok index)
      (read : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
        before.frames index = .ok (frame, restore))
      (progress : ElsePrefix ops state before frame restore status after) :
      ElseEffect ops state before status after

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status, after)) :
    ElseEffect ops state before status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at called
  simp only [alloc.vec.Vec.is_empty, bind_ok] at called
  cases empty : before.frames.val.isEmpty with
  | true =>
    simp only [empty, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at called
    obtain ⟨rfl, rfl⟩ := called
    exact .empty empty
  | false =>
    simp only [empty, Bool.false_eq_true, ↓reduceIte] at called
    obtain ⟨index, subtracted, rest⟩ := bind_ok_inv _ _ _ called
    obtain ⟨⟨frame, restore⟩, read, rest⟩ := bind_ok_inv _ _ _ rest
    apply ElseEffect.selected empty subtracted read
    simp only [uncurry_apply_pair, core.option.Option.take] at rest
    cases live : before.reachable with
    | false =>
      simp only [live, Bool.false_eq_true, ↓reduceIte] at rest
      apply ElsePrefix.dead live
      cases guard : frame.if_pc with
      | none =>
        apply ElseFinish.unguarded
        simpa only [guard, elsePrepared, live] using rest
      | some guardPc =>
        simp only [guard] at rest
        obtain ⟨⟨answer, counted⟩, countCall, tail⟩ := bind_ok_inv _ _ _ rest
        have countCall' : runtime.compiler.FunctionCompiler.pc ops (elsePrepared before frame restore before.budget frame.fixups) = .ok (answer, counted) := by
          simpa only [elsePrepared, live] using countCall
        cases answer with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl⟩ := tail
          exact .pcRejected countCall'
        | Ok target =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
          obtain ⟨⟨answer, patched⟩, patchCall, tail⟩ := bind_ok_inv _ _ _ tail
          cases answer with
          | Err error =>
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
            obtain ⟨rfl, rfl⟩ := tail
            exact .patchRejected countCall' patchCall
          | Ok unitValue =>
            cases unitValue
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
            exact .guarded countCall' patchCall tail
    | true =>
      simp only [live, ↓reduceIte] at rest
      obtain ⟨⟨result, budget, fixups⟩, reserved, rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        simpa only [elsePrepared, live] using (ElsePrefix.reserveRejected (state := state) (restore := restore) live reserved)
      | Ok unitValue =>
        cases unitValue
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok] at rest
        obtain ⟨⟨result, emitted⟩, emitCall, rest⟩ := bind_ok_inv _ _ _ rest
        cases result with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, rfl⟩ := rest
          apply ElsePrefix.emitRejected live reserved
          simpa only [elsePrepared, live] using emitCall
        | Ok unitValue =>
          cases unitValue
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok] at rest
          apply ElsePrefix.emitted live reserved (by simpa only [elsePrepared, live] using emitCall)
          cases guard : frame.if_pc with
          | none =>
            apply ElseFinish.unguarded
            simpa only [guard] using rest
          | some guardPc =>
            simp only [guard] at rest
            obtain ⟨⟨answer, counted⟩, countCall, tail⟩ := bind_ok_inv _ _ _ rest
            have countCall' : runtime.compiler.FunctionCompiler.pc ops emitted = .ok (answer, counted) := by
              simpa only [] using countCall
            cases answer with
            | Err error =>
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
              obtain ⟨rfl, rfl⟩ := tail
              exact .pcRejected countCall'
            | Ok target =>
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
              obtain ⟨⟨answer, patched⟩, patchCall, tail⟩ := bind_ok_inv _ _ _ tail
              cases answer with
              | Err error =>
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
                obtain ⟨rfl, rfl⟩ := tail
                exact .patchRejected countCall' patchCall
              | Ok unitValue =>
                cases unitValue
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
                exact .guarded countCall' patchCall tail

/-- Else callbacks change work buffers and reachability, never source layout,
control maps, or auxiliary tables. This holds without allocator laws. -/
def ElseFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with budget := after.budget, before := after.before, height := after.height, next_source := after.next_source, frames := after.frames, reachable := after.reachable, function := {before.function with code := after.function.code, source_offsets := after.function.source_offsets, max_stack := after.function.max_stack, slot_count := after.function.slot_count}}

theorem ElseFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : ElseFrame before middle) (second : ElseFrame middle after) : ElseFrame before after := by
  unfold ElseFrame at *
  rw [second, first]

/-- Primitive else stages preserve the physical frame vector; allocator laws
are required only for the slot monotonicity consequence. -/
structure ElseTransport {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) : Prop where
  frame : ElseFrame before after
  frames : after.frames = before.frames
  slots : Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val

theorem ElseTransport.trans {A : Type} {ops : runtime.platform.Alloc A}
    {before middle after : runtime.compiler.FunctionCompiler A}
    (first : ElseTransport ops before middle) (second : ElseTransport ops middle after) :
    ElseTransport ops before after :=
  ⟨first.frame.trans second.frame, second.frames.trans first.frames,
    fun law => (first.slots law).trans (second.slots law)⟩

private theorem else_pc_transport {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (status)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    ElseTransport ops before after := by
  have post := compiler_pc ops before
  rw [called, WP.spec_ok] at post
  obtain ⟨_, _, budget, same⟩ := post
  change after = {before with budget} at same
  rw [same]
  exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem else_patch_transport {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32) (status)
    (called : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    ElseTransport ops before after := by
  rcases compiler_patch_cases ops before after pc target status called with rfl | ⟨instruction, code, rfl, _⟩
  all_goals exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem else_emit_transport {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr) (status)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    ElseTransport ops before after := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status called).1
  change after = _ at frame
  rw [frame]
  exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem else_observe_transport {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (status)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    ElseTransport ops before after := by
  have frame := compiler_observe_frame_raw ops before state status after called
  refine ⟨?_, ?_, fun law => ?_⟩
  · unfold ElseFrame
    rw [frame]
  · rw [frame]
  · have post := compiler_observe_inv ops law before state
    rw [called, WP.spec_ok] at post
    exact post.2

theorem ElseFinish.transport {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {guard : Option Usize} {before after : runtime.compiler.FunctionCompiler A}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseFinish ops state guard before status after) : ElseTransport ops before after := by
  cases effect with
  | unguarded observed => exact else_observe_transport ops _ _ state _ observed
  | pcRejected counted => exact else_pc_transport ops _ _ _ counted
  | patchRejected counted patched => exact (else_pc_transport ops _ _ _ counted).trans (else_patch_transport ops _ _ _ _ _ patched)
  | guarded counted patched observed =>
    exact ((else_pc_transport ops _ _ _ counted).trans (else_patch_transport ops _ _ _ _ _ patched)).trans
      (else_observe_transport ops _ _ state _ observed)

/-- The prefix chooses the new frame once; every later stage retains it. -/
theorem ElsePrefix.transport {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {frame : runtime.compiler.Frame}
    {restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElsePrefix ops state before frame restore status after) :
    ∃ fixups, ElseTransport ops {before with frames := restore {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups}} after := by
  have prepared : ∀ budget fixups, ElseTransport ops
      {before with frames := restore {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups}}
      (elsePrepared before frame restore budget fixups) := fun _ _ => ⟨rfl, rfl, fun _ => Nat.le_refl _⟩
  cases effect with
  | dead dead finished => exact ⟨_, (prepared _ _).trans finished.transport⟩
  | reserveRejected live reserved => exact ⟨_, ⟨rfl, rfl, fun _ => Nat.le_refl _⟩⟩
  | emitRejected live reserved emitted => exact ⟨_, (prepared _ _).trans (else_emit_transport ops _ _ _ _ emitted)⟩
  | emitted live reserved emitted finished =>
    exact ⟨_, ((prepared _ _).trans (else_emit_transport ops _ _ _ _ emitted)).trans finished.transport⟩

theorem ElseEffect.transport {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseEffect ops state before status after) :
    ∃ frames, ElseTransport ops {before with frames} after := by
  cases effect with
  | empty empty => exact ⟨_, ⟨rfl, rfl, fun _ => Nat.le_refl _⟩⟩
  | selected nonempty subtracted read progress =>
    obtain ⟨fixups, retained⟩ := progress.transport
    exact ⟨_, retained⟩

theorem ElseEffect.frame {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseEffect ops state before status after) : ElseFrame before after := by
  obtain ⟨frames, retained⟩ := effect.transport
  exact (show ElseFrame before {before with frames} from rfl).trans retained.frame

/-- Normality requires numeric space only for a live fallthrough and a genuine
branch instruction wherever the original frame retains a guard fixup. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior ++ [frame])
    (guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ kind old, before.function.code.val[guard.val]? = some (BranchKind.instruction kind old))
    (space : before.reachable = true → frame.fixups.val.length < Usize.max ∧
      before.function.code.val.length < Usize.max ∧ before.function.source_offsets.val.length < Usize.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt ⦃ _ => True ⦄ := by
  have nonempty : before.frames.val.isEmpty = false := by
    rw [frames]
    cases prior <;> rfl
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by
    simp only [frames, alloc.vec.Vec.len, List.length_append, List.length_singleton] at indexEq
    scalar_tac
  step as ⟨found, restore, foundEq, restoreEq⟩
  have same : found = frame := by
    simpa only [frames, atLast, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero] using foundEq
  rw [same]
  cases live : before.reachable with
  | false =>
    simp only [core.option.Option.take, live, Bool.false_eq_true, ite_false, Bool.or_false]
    cases guardEq : frame.if_pc with
    | none =>
      exact WP.spec_mono (compiler_observe ops law _ state) (fun _ _ => trivial)
    | some guard =>
      obtain ⟨kind, old, site⟩ := guardSites guard guardEq
      step with compiler_pc ops _ as ⟨result, counted, _, _, budget, countedEq⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok target =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have retained : counted.function.code.val[guard.val]? = some (kind.instruction old) := by
          rw [countedEq]
          exact site
        step with runtime.compiler.control.FunctionCompiler.patch.available ops counted guard kind old target retained
          as ⟨result, patched, accepted, effect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact WP.spec_mono (compiler_observe ops law patched state) (fun _ _ => trivial)
  | true =>
    obtain ⟨fixupsFit, codeFits, sourcesFit, coordinateFits⟩ := space live
    simp only [core.option.Option.take, live, ite_true, Bool.or_true]
    step with budget_push ops law before.budget frame.fixups (alloc.vec.Vec.len before.function.code) fixupsFit
      as ⟨result, budget, fixups, effect⟩
    cases result with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      let prepared := { before with budget := budget, reachable := frame.entry_reachable, frames := restore { frame with kind := .Else, if_pc := none, end_reachable := true, fixups := fixups } }
      step with compiler_emit ops law prepared (.Jump core.num.U32.MAX)
        (show prepared.function.code.val.length < Usize.max from codeFits)
        (show prepared.function.source_offsets.val.length < Usize.max from sourcesFit)
        (show prepared.function.body_start.val + prepared.next_source.val ≤ Usize.max from coordinateFits)
        as ⟨result, emitted, effect⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        cases guardEq : frame.if_pc with
        | none => exact WP.spec_mono (compiler_observe ops law emitted state) (fun _ _ => trivial)
        | some guard =>
          obtain ⟨kind, old, site⟩ := guardSites guard guardEq
          have retained : emitted.function.code.val[guard.val]? = some (kind.instruction old) := by
            obtain ⟨budget, code, sources, same, appended, _⟩ := effect rfl
            rw [same]
            change code.val[guard.val]? = _
            rw [appended]
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp site).1]
            exact site
          step with compiler_pc ops emitted as ⟨result, counted, _, _, budget, countedEq⟩
          cases result with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          | Ok target =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            have countedSite : counted.function.code.val[guard.val]? = some (kind.instruction old) := by
              rw [countedEq]
              exact retained
            step with runtime.compiler.control.FunctionCompiler.patch.available ops counted guard kind old target countedSite
              as ⟨result, patched, accepted, effect⟩
            rw [accepted]
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact WP.spec_mono (compiler_observe ops law patched state) (fun _ _ => trivial)


/-- Frame, guard, and allocation facts for available else callbacks. -/
structure ElseAvailableInputs {A : Type} (bound : Nat)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) where
  frame : runtime.compiler.Frame
  prior : List runtime.compiler.Frame
  frames : before.frames.val = prior ++ [frame]
  guardSites : ∀ guard, frame.if_pc = some guard →
    ∃ kind old, before.function.code.val[guard.val]? = some (BranchKind.instruction kind old)
  guardPc : frame.if_pc ≠ none → before.function.code.length + (if before.reachable then 1 else 0) ≤ U32.max
  request : state.vals.length ≤ bound
  slotsFit : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max
  space : before.reachable = true →
    frame.fixups.length < Usize.max ∧ frame.fixups.length + 1 ≤ bound ∧
    before.function.code.length ≤ U32.max ∧ before.function.code.length < Usize.max ∧
    before.function.source_offsets.length < Usize.max ∧ before.function.code.length + 1 ≤ bound ∧
    before.function.source_offsets.length + 1 ≤ bound ∧
    before.function.body_start.val + before.next_source.val ≤ Usize.max ∧
    before.budget.instructions.val < before.budget.limits.max_instructions.val

/-- Frame and guard premises for the successful live else effect. -/
structure ElseLiveSuccessInputs {A : Type} (before : runtime.compiler.FunctionCompiler A) where
  frame : runtime.compiler.Frame
  prior : List runtime.compiler.Frame
  guard : Usize
  condition : U32
  old : U32
  target : U32
  frames : before.frames.val = prior ++ [frame]
  live : before.reachable = true
  guardPc : frame.if_pc = some guard
  site : before.function.code.val[guard.val]? = some (.JumpIfZero condition old)
  position : target.val = before.function.code.val.length + 1

/-- Available allocation preserves every budget field except the single live
fallthrough instruction charge. Dormant arms need no emission capacity. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (inputs : ElseAvailableInputs bound before state) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (if before.reachable then 1 else 0) ⦄ := by
  rcases inputs with ⟨frame, prior, frames, guardSites, guardPc, request, slotsFit, space⟩
  have nonempty : before.frames.val.isEmpty = false := by
    rw [frames]
    cases prior <;> rfl
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by
    simp only [frames, alloc.vec.Vec.len, List.length_append, List.length_singleton] at indexEq
    scalar_tac
  step as ⟨found, restore, foundEq, restoreEq⟩
  have same : found = frame := by
    simpa only [frames, atLast, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero] using foundEq
  rw [same]
  cases live : before.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.or_false]
    let prepared := {before with frames := restore {frame with kind := .Else, if_pc := none}, reachable := frame.entry_reachable}
    have finish (compiler : runtime.compiler.FunctionCompiler A)
        (budgetEq : compiler.budget = before.budget)
        (localEq : compiler.function.local_slots = before.function.local_slots) :
        runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ (status, after) =>
          status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
            used.val = before.budget.instructions.val + 0 ⦄ := by
      apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state request
        (by rw [localEq]; exact slotsFit))
      rintro ⟨status, after⟩ ⟨accepted, kept⟩
      refine ⟨accepted, before.budget.instructions, ?_, ?_⟩
      · simpa only [budgetEq] using kept
      · simp only [live, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases guardEq : frame.if_pc with
    | none => exact finish prepared rfl rfl
    | some guard =>
      obtain ⟨kind, old, site⟩ := guardSites guard guardEq
      have pcFits : prepared.function.code.length ≤ U32.max := by
        have fits := guardPc (by rw [guardEq]; exact Option.some_ne_none guard)
        simpa only [live, Bool.false_eq_true, ite_false, Nat.add_zero] using fits
      step with compiler_pc_available ops prepared pcFits as ⟨status, counted, same, target, accepted, targetEq⟩
      subst counted
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.control.FunctionCompiler.patch.available ops prepared guard kind old target site
        as ⟨status, patched, accepted, effect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨code, patchedEq, _⟩ := effect
      exact finish patched (by rw [patchedEq]) (by rw [patchedEq])
  | true =>
    obtain ⟨fixupsFit, fixupsRequest, pcFit, codeFit, sourceFit, codeRequest, sourceRequest, coordinate, room⟩ := space live
    simp only [ite_true, Bool.or_true]
    step with budget_push_available ops bound available before.budget frame.fixups (alloc.vec.Vec.len before.function.code)
      fixupsFit fixupsRequest as ⟨status, budget, fixups, accepted, same, appended⟩
    subst status budget
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let prepared := {before with frames := restore {frame with kind := .Else, if_pc := none, end_reachable := true, fixups}, reachable := frame.entry_reachable}
    step with runtime.compiler.FunctionCompiler.emit.available ops bound available prepared (.Jump core.num.U32.MAX)
      (show prepared.function.code.length ≤ U32.max from pcFit)
      (show prepared.function.code.length < Usize.max from codeFit)
      (show prepared.function.source_offsets.length < Usize.max from sourceFit)
      (show prepared.function.code.length + 1 ≤ bound from codeRequest)
      (show prepared.function.source_offsets.length + 1 ≤ bound from sourceRequest)
      (show prepared.function.body_start.val + prepared.next_source.val ≤ Usize.max from coordinate)
      (show prepared.budget.instructions.val < prepared.budget.limits.max_instructions.val from room)
      as ⟨status, emitted, accepted, effect⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨used, code, sources, emittedEq, usedEq, codeAppend, sourcesAppend⟩ := effect
    have finish (compiler : runtime.compiler.FunctionCompiler A)
        (budgetEq : compiler.budget = {before.budget with instructions := used})
        (localEq : compiler.function.local_slots = before.function.local_slots) :
        runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ (status, after) =>
          status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
            used.val = before.budget.instructions.val + 1 ⦄ := by
      apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state request
        (by rw [localEq]; exact slotsFit))
      rintro ⟨status, after⟩ ⟨accepted, kept⟩
      refine ⟨accepted, used, kept.trans budgetEq, ?_⟩
      simpa only [live, ite_true] using usedEq
    cases guardEq : frame.if_pc with
    | none => exact finish emitted (by rw [emittedEq]) (by rw [emittedEq])
    | some guard =>
      obtain ⟨kind, old, site⟩ := guardSites guard guardEq
      have pcFits : emitted.function.code.length ≤ U32.max := by
        have fits := guardPc (by rw [guardEq]; exact Option.some_ne_none guard)
        simpa only [emittedEq, alloc.vec.Vec.length, codeAppend, List.length_append,
          List.length_singleton, live, ite_true] using fits
      have retained : emitted.function.code.val[guard.val]? = some (kind.instruction old) := by
        rw [emittedEq]
        change code.val[guard.val]? = _
        rw [codeAppend, List.getElem?_append_left (List.getElem?_eq_some_iff.mp site).1]
        exact site
      step with compiler_pc_available ops emitted pcFits as ⟨status, counted, same, target, accepted, targetEq⟩
      subst counted
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.control.FunctionCompiler.patch.available ops emitted guard kind old target retained
        as ⟨status, patched, accepted, effect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨code, patchedEq, _⟩ := effect
      exact finish patched (by rw [patchedEq, emittedEq]) (by rw [patchedEq, emittedEq])

theorem ElseEffect.capacity {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseEffect ops state before status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  obtain ⟨frames, retained⟩ := effect.transport
  exact retained.slots law

/-- Select the original final frame from the callback's checked index/read. -/
theorem ElseEffect.last_frame {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseEffect ops state before status after) (frame : runtime.compiler.Frame)
    (prior : List runtime.compiler.Frame) (frames : before.frames.val = prior ++ [frame]) :
    ∃ index restore, index.val = prior.length ∧ restore = before.frames.set index ∧
      ElsePrefix ops state before frame restore status after := by
  cases effect with
  | empty empty =>
    rw [frames] at empty
    cases prior <;> cases empty
  | @selected index found restore status after nonempty subtracted read progress =>
    have arithmetic := UScalar.sub_equiv (alloc.vec.Vec.len before.frames) 1#usize
    rw [subtracted] at arithmetic
    have valueEq : (alloc.vec.Vec.len before.frames).val = index.val + 1 := arithmetic.2.1
    have lastIndex : index.val = prior.length := by
      simp only [alloc.vec.Vec.len, frames, List.length_append, List.length_singleton, Usize.ofNatCore_val_eq] at valueEq
      omega
    have inside : index.val < before.frames.length := by
      simp only [alloc.vec.Vec.length, frames, List.length_append, List.length_singleton, lastIndex]
      omega
    have selected := alloc.vec.Vec.index_mut_usize_spec before.frames index inside
    rw [← alloc.vec.Vec.index_mut_slice_index, read, WP.spec_ok] at selected
    obtain ⟨foundEq, restoreEq⟩ := selected
    have same : found = frame := by
      simpa only [frames, lastIndex, Std.le_refl, List.getElem_append_right,
        tsub_self, List.getElem_cons_zero] using foundEq
    rw [same] at progress
    exact ⟨index, restore, lastIndex, restoreEq, progress⟩

/-- A successful tail keeps the selected frame and source offsets; its optional
patch changes no instruction count. Observation records the supplied cursor. -/
theorem ElseFinish.success_fields {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {guard : Option Usize} {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseFinish ops state guard before (.Ok ()) after) (law : Platform.AllocCorrect ops) :
    after.frames = before.frames ∧ after.reachable = before.reachable ∧
    after.function.code.val.length = before.function.code.val.length ∧
    after.function.source_offsets = before.function.source_offsets ∧ after.next_source = state.pos := by
  have observedFields (compiler changed : runtime.compiler.FunctionCompiler A)
      (called : runtime.compiler.FunctionCompiler.observe ops compiler state = .ok (.Ok (), changed)) :
      changed.frames = compiler.frames ∧ changed.reachable = compiler.reachable ∧
      changed.function.code = compiler.function.code ∧
      changed.function.source_offsets = compiler.function.source_offsets ∧ changed.next_source = state.pos := by
    have post := compiler_observe ops law compiler state
    rw [called, WP.spec_ok] at post
    have fields := post rfl
    exact ⟨fields.2.2.2.2.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.1,
      fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1⟩
  cases effect with
  | unguarded observed =>
    obtain ⟨frames, reachable, code, sources, cursor⟩ := observedFields _ _ observed
    exact ⟨frames, reachable, congrArg (fun code => code.val.length) code, sources, cursor⟩
  | guarded counted patched observed =>
    have countPost := compiler_pc ops before
    rw [counted, WP.spec_ok] at countPost
    obtain ⟨_, _, budget, same⟩ := countPost
    dsimp only at same
    obtain ⟨frames, reachable, code, sources, cursor⟩ := observedFields _ _ observed
    rcases compiler_patch_cases ops _ _ _ _ _ patched with unchanged | ⟨instruction, changedCode, patchEq, codeEq⟩
    · rw [unchanged, same] at frames reachable code sources
      exact ⟨frames, reachable, congrArg (fun code => code.val.length) code, sources, cursor⟩
    · rw [patchEq, same] at frames reachable code sources
      refine ⟨frames, reachable, ?_, sources, cursor⟩
      rw [code, codeEq, List.length_set, same]

/-- Successful closure publishes exactly the updated selected frame and one
matching instruction/source entry for a live fallthrough. -/
theorem ElsePrefix.success_fields {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {frame : runtime.compiler.Frame}
    {restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame}
    (effect : ElsePrefix ops state before frame restore (.Ok ()) after) (law : Platform.AllocCorrect ops) :
    ∃ fixups, (if before.reachable then fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len before.function.code]
        else fixups = frame.fixups) ∧
      after.frames = restore {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups} ∧
      after.reachable = frame.entry_reachable ∧
      after.function.code.val.length = before.function.code.val.length + (if before.reachable then 1 else 0) ∧
      after.function.source_offsets.val.map UScalar.val = before.function.source_offsets.val.map UScalar.val ++
        (if before.reachable then [before.function.body_start.val + before.next_source.val] else []) ∧
      after.next_source = state.pos := by
  cases effect with
  | dead dead finished =>
    obtain ⟨frames, reachable, code, sources, cursor⟩ := finished.success_fields law
    refine ⟨frame.fixups, ?_, frames, reachable, ?_, ?_, cursor⟩
    · simp only [dead, Bool.false_eq_true, ite_false]
    · simpa only [elsePrepared, dead, Bool.false_eq_true, ite_false, Nat.add_zero] using code
    · simp only [sources, elsePrepared, dead, Bool.false_eq_true, ite_false, List.append_nil]
  | emitted live reserved emitted finished =>
    obtain ⟨budgetEq, appended⟩ := budget_push_success ops law _ _ _ _ _ reserved
    have exactEmit := (runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ emitted).2 law |>.2 rfl
    obtain ⟨used, code, sources, emittedEq, _, codeAppend, sourceAppend⟩ := exactEmit
    obtain ⟨frames, reachable, length, sourceEq, cursor⟩ := finished.success_fields law
    rw [emittedEq] at frames reachable length sourceEq
    refine ⟨_, ?_, frames, reachable, ?_, ?_, cursor⟩
    · simpa only [live, ite_true] using appended
    · simpa only [elsePrepared, codeAppend, List.length_append, List.length_singleton, live, ite_true] using length
    · simpa only [sourceEq, elsePrepared, live, ite_true] using sourceAppend
/-- A successful owned guard patches exactly its branch target, preserving the
selected frame and reachability through final observation. -/
theorem ElseFinish.guard_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {guard : Usize}
    (effect : ElseFinish ops state (some guard) before (.Ok ()) after)
    (condition old target : U32)
    (site : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = before.function.code.val.length) :
    after.function.code.val = before.function.code.val.set guard.val (.JumpIfZero condition target) := by
  cases effect with
  | @guarded guard before actual counted patched status after countCall patchCall observed =>
    have countPost := compiler_pc ops before
    rw [countCall, WP.spec_ok] at countPost
    obtain ⟨_, targetEq, budget, same⟩ := countPost
    dsimp only at targetEq same
    have targetSame : actual = target := by
      apply UScalar.eq_of_val_eq
      exact (targetEq actual rfl).trans position.symm
    subst actual
    have patchPost := runtime.compiler.control.FunctionCompiler.patch.available ops counted guard (.zero condition) old target
      (by rw [same]; exact site)
    rw [patchCall, WP.spec_ok] at patchPost
    obtain ⟨_, code, patchedEq, codeEq⟩ := patchPost
    dsimp only at patchedEq codeEq
    have observedFrame := compiler_observe_frame_raw ops patched state (.Ok ()) after observed
    rw [observedFrame, patchedEq]
    change code.val = _
    simpa only [same, BranchKind.instruction] using codeEq

theorem ElseEffect.live_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseEffect ops state before (.Ok ()) after) (law : Platform.AllocCorrect ops)
    (inputs : ElseLiveSuccessInputs before) :
    after.reachable = inputs.frame.entry_reachable ∧
      after.function.code.val = (before.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set
        inputs.guard.val (.JumpIfZero inputs.condition inputs.target) ∧
      ∃ fixups, fixups.val = inputs.frame.fixups.val ++ [alloc.vec.Vec.len before.function.code] ∧
        after.frames.val = inputs.prior ++ [{inputs.frame with kind := .Else, if_pc := none, end_reachable := true, fixups}] := by
  rcases inputs with ⟨frame, prior, guard, condition, old, target, frames, live, guardPc, site, position⟩
  obtain ⟨index, restore, lastIndex, restoreEq, progress⟩ := effect.last_frame frame prior frames
  obtain ⟨fixups, appended, finalFrames, finalReach, length, sources, cursor⟩ := progress.success_fields law
  simp only [live, ite_true] at appended
  have published : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none, end_reachable := true, fixups}] := by
    rw [finalFrames, restoreEq, alloc.vec.Vec.set_val_eq]
    simp only [frames, lastIndex, live, Bool.or_true, Std.le_refl, List.set_append_right, tsub_self, List.set_cons_zero]
  refine ⟨finalReach, ?_, fixups, appended, published⟩
  cases progress with
  | dead dead finished => simp only [live, Bool.true_eq_false] at dead
  | @emitted budget updated middle status after live reserved emitted finished =>
    have exactEmit := (runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ emitted).2 law |>.2 rfl
    obtain ⟨used, code, offsets, emittedEq, _, codeAppend, _⟩ := exactEmit
    have retained : middle.function.code.val[guard.val]? = some (.JumpIfZero condition old) := by
      rw [emittedEq]
      change code.val[guard.val]? = _
      rw [codeAppend]
      change (before.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX])[guard.val]? = _
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp site).1]
      exact site
    have targetPosition : target.val = middle.function.code.val.length := by
      simpa only [emittedEq, codeAppend, elsePrepared, List.length_append, List.length_singleton] using position
    rw [guardPc] at finished
    have codeEq := finished.guard_success condition old target retained targetPosition
    simpa only [emittedEq, codeAppend, elsePrepared] using codeEq

theorem ElseEffect.dead_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseEffect ops state before (.Ok ()) after) (law : Platform.AllocCorrect ops)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : before.frames.val = prior ++ [frame]) (dead : before.reachable = false) :
    after.reachable = frame.entry_reachable ∧
      after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}] ∧
      ∃ restore, ElseFinish ops state frame.if_pc (elsePrepared before frame restore before.budget frame.fixups) (.Ok ()) after := by
  obtain ⟨index, restore, lastIndex, restoreEq, progress⟩ := effect.last_frame frame prior frames
  obtain ⟨fixups, appended, finalFrames, reachable, length, sources, cursor⟩ := progress.success_fields law
  simp only [dead, Bool.false_eq_true, ite_false] at appended
  subst fixups
  have published : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}] := by
    rw [finalFrames, restoreEq, alloc.vec.Vec.set_val_eq]
    simp only [frames, lastIndex, dead, Bool.or_false, Std.le_refl, List.set_append_right, tsub_self, List.set_cons_zero]
  refine ⟨reachable, published, ?_⟩
  cases progress with
  | dead dead finished => exact ⟨restore, finished⟩
  | emitted live reserved emitted finished => simp only [dead, Bool.false_eq_true] at live
/-- Before final observation the callback has not changed the retained slot bounds. -/
theorem ElseFinish.observation_slots {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {guard : Option Usize} {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseFinish ops state guard before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) ∧
      middle.function.slot_count = before.function.slot_count ∧
      middle.function.local_slots = before.function.local_slots := by
  cases effect with
  | unguarded observed => exact ⟨_, observed, rfl, rfl⟩
  | guarded counted patched observed =>
    have countPost := compiler_pc ops before
    rw [counted, WP.spec_ok] at countPost
    obtain ⟨_, _, budget, same⟩ := countPost
    dsimp only at same
    refine ⟨_, observed, ?_, ?_⟩ <;>
      rcases compiler_patch_cases ops _ _ _ _ _ patched with unchanged | ⟨instruction, code, patchEq, codeEq⟩
    all_goals first | rw [unchanged, same] | rw [patchEq, same]

theorem ElseEffect.observation_slots {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseEffect ops state before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) ∧
      middle.function.slot_count = before.function.slot_count ∧
      middle.function.local_slots = before.function.local_slots := by
  cases effect with
  | selected nonempty subtracted read progress =>
    cases progress with
    | dead dead finished => exact finished.observation_slots
    | emitted live reserved emitted finished =>
      obtain ⟨middle, observed, slots, locals⟩ := finished.observation_slots
      have frame := (runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ emitted).1
      refine ⟨middle, observed, ?_, ?_⟩
      · rw [slots, frame]; rfl
      · rw [locals, frame]; rfl

theorem ElseEffect.observation {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : ElseEffect ops state before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  obtain ⟨middle, observed, _, _⟩ := effect.observation_slots
  exact ⟨middle, observed⟩

/-- Optional patching and observation never change the selected physical frames. -/
theorem ElseFinish.frames {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {guard : Option Usize} {before after : runtime.compiler.FunctionCompiler A}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElseFinish ops state guard before status after) : after.frames = before.frames := by
  exact effect.transport.frames

theorem ElsePrefix.frames {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {frame : runtime.compiler.Frame}
    {restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ElsePrefix ops state before frame restore status after) :
    ∃ fixups, after.frames = restore {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups} := by
  obtain ⟨fixups, retained⟩ := effect.transport
  exact ⟨fixups, retained.frames⟩

end Itasca.Runtime.Compiler
