import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-! Staged contracts for closing a control frame. The guard patch, fixup loop,
map publication, optional function return and observation retain their actual
intermediate states, including every normally returned error. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Reachability after joining the fallthrough, branches, and an absent else arm. -/
def endReachable (before : Bool) (frame : runtime.compiler.Frame) : Bool :=
  before || frame.end_reachable || (match frame.kind with | .Then => frame.entry_reachable | _ => false)

/-- Closing a map publishes its end coordinates before the optional return. -/
def endPublished {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (map : runtime.compiler.ControlMap)
    (restore : runtime.compiler.ControlMap → alloc.vec.Vec runtime.compiler.ControlMap)
    (target source : Usize) : runtime.compiler.FunctionCompiler A :=
  {before with function := {before.function with controls := restore {map with source_end := source, end_pc := target}}, reachable := endReachable before.reachable frame}

/-- The last optional return and observation after publishing the closed map. -/
inductive EndFinish {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (frame : runtime.compiler.Frame) (before : runtime.compiler.FunctionCompiler A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | nested {status after} (nonBody : frame.kind ≠ .Body)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      EndFinish ops state frame before status after
  | returnRejected {error after} (body : frame.kind = .Body)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before
        (.Return frame.height (if before.reachable then frame.results else 0#u32)) = .ok (.Err error, after)) :
      EndFinish ops state frame before (.Err error) after
  | returned {middle status after} (body : frame.kind = .Body)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before
        (.Return frame.height (if before.reachable then frame.results else 0#u32)) = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops middle state = .ok (status, after)) :
      EndFinish ops state frame before status after

/-- The control-map read and both checked byte-coordinate operations. -/
def EndPublication {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (frame : runtime.compiler.Frame) (target : U32) (before : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError) (after : runtime.compiler.FunctionCompiler A) : Prop :=
  ∃ map restore targetIndex source,
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.ControlMap)
      before.function.controls frame.map = .ok (map, restore) ∧
    lift (UScalar.cast .Usize target) = .ok targetIndex ∧
    (before.function.body_start + state.pos : Result Usize) = .ok source ∧
    EndFinish ops state frame (endPublished before frame map restore targetIndex source) status after

/-- Both generated fixup loops have the same snapshot signature and exact call
witness; the tag records which branch of the callback selected the loop. -/
def EndLoopCall {A : Type} (ops : runtime.platform.Alloc A) (guarded : Bool)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError) (after : runtime.compiler.FunctionCompiler A) : Prop :=
  (if guarded then runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
    else runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0)
    ops before sites target 0#usize (.Ok ()) = .ok (compilerSnapshot after status)

/-- Normal loop rejection returns the exact snapshot without map publication. -/
inductive EndLoopEffect {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (frame : runtime.compiler.Frame) (target : U32) (guarded : Bool)
    (before : runtime.compiler.FunctionCompiler A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | rejected {error after} (called : EndLoopCall ops guarded before frame.fixups target (.Err error) after) :
      EndLoopEffect ops state frame target guarded before (.Err error) after
  | published {middle status after} (called : EndLoopCall ops guarded before frame.fixups target (.Ok ()) middle)
      (publication : EndPublication ops state frame target middle status after) :
      EndLoopEffect ops state frame target guarded before status after

/-- The selected guard patch precedes the fixup loop and can reject normally. -/
inductive EndGuardEffect {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (frame : runtime.compiler.Frame) (target : U32) (before : runtime.compiler.FunctionCompiler A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | unguarded {status after} (guard : frame.if_pc = none)
      (loop : EndLoopEffect ops state frame target false before status after) :
      EndGuardEffect ops state frame target before status after
  | rejected {guard error after} (selected : frame.if_pc = some guard)
      (patched : runtime.compiler.control.FunctionCompiler.patch ops before guard target = .ok (.Err error, after)) :
      EndGuardEffect ops state frame target before (.Err error) after
  | guarded {guard middle status after} (selected : frame.if_pc = some guard)
      (patched : runtime.compiler.control.FunctionCompiler.patch ops before guard target = .ok (.Ok (), middle))
      (loop : EndLoopEffect ops state frame target true middle status after) :
      EndGuardEffect ops state frame target before status after

/-- Popping the frame happens before the PC check and remains visible on error. -/
inductive EndEffect {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (before : runtime.compiler.FunctionCompiler A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | empty {frames} (popped : alloc.vec.Vec.pop Global before.frames = .ok (none, frames)) :
      EndEffect ops state before (.Err .OutOfMemory) {before with frames}
  | pcRejected {frame frames error after}
      (popped : alloc.vec.Vec.pop Global before.frames = .ok (some frame, frames))
      (counted : runtime.compiler.FunctionCompiler.pc ops {before with frames} = .ok (.Err error, after)) :
      EndEffect ops state before (.Err error) after
  | counted {frame frames target middle status after}
      (popped : alloc.vec.Vec.pop Global before.frames = .ok (some frame, frames))
      (count : runtime.compiler.FunctionCompiler.pc ops {before with frames} = .ok (.Ok target, middle))
      (guard : EndGuardEffect ops state frame target middle status after) :
      EndEffect ops state before status after

/-- Every normal return exposes the selected frame and all completed stages. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (status, after)) :
    EndEffect ops state before status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at called
  obtain ⟨⟨selected, frames⟩, popped, rest⟩ := bind_ok_inv _ _ _ called
  cases selected with
  | none =>
    simp only [uncurry_apply_pair, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact .empty popped
  | some frame =>
    simp only [uncurry_apply_pair, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨answer, counted⟩, countCall, tail⟩ := bind_ok_inv _ _ _ rest
    cases answer with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact .pcRejected popped countCall
    | Ok target =>
      apply EndEffect.counted popped countCall
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      cases guardEq : frame.if_pc with
      | none =>
        apply EndGuardEffect.unguarded guardEq
        simp only [guardEq] at tail
        obtain ⟨⟨signatures, slots, budget, batch, fn, frames, live, cursor, operands, height, offsets, depths, result⟩, loopCall, tail⟩ := bind_ok_inv _ _ _ tail
        let current : runtime.compiler.FunctionCompiler A := ⟨signatures, slots, budget, batch, fn, frames, live, cursor, operands, height, offsets, depths⟩
        cases result with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl⟩ := tail
          exact .rejected loopCall
        | Ok unitValue =>
          cases unitValue
          refine EndLoopEffect.published (middle := current) ?_ ?_
          · exact loopCall
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
          obtain ⟨⟨map, restore⟩, read, tail⟩ := bind_ok_inv _ _ _ tail
          simp only [uncurry_apply_pair] at tail
          obtain ⟨targetIndex, cast, tail⟩ := bind_ok_inv _ _ _ tail
          obtain ⟨source, added, tail⟩ := bind_ok_inv _ _ _ tail
          refine ⟨map, restore, targetIndex, source, read, cast, added, ?_⟩
          cases liveEq : live <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
            simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair] at tail
          all_goals first
            | apply EndFinish.nested (by rw [kindEq]; intro impossible; cases impossible)
              simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or] using tail
            | obtain ⟨⟨answer, emitted⟩, emitCall, tail⟩ := bind_ok_inv _ _ _ tail
              cases answer with
              | Err error =>
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
                obtain ⟨rfl, rfl⟩ := tail
                apply EndFinish.returnRejected kindEq
                simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true] using emitCall
              | Ok unitValue =>
                cases unitValue
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
                apply EndFinish.returned kindEq _ tail
                simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true] using emitCall
      | some guard =>
        simp only [guardEq] at tail
        obtain ⟨⟨answer, patched⟩, patchCall, tail⟩ := bind_ok_inv _ _ _ tail
        cases answer with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl⟩ := tail
          exact .rejected guardEq patchCall
        | Ok unitValue =>
          cases unitValue
          apply EndGuardEffect.guarded guardEq patchCall
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
          obtain ⟨⟨signatures, slots, budget, batch, fn, frames, live, cursor, operands, height, offsets, depths, result⟩, loopCall, tail⟩ := bind_ok_inv _ _ _ tail
          let current : runtime.compiler.FunctionCompiler A := ⟨signatures, slots, budget, batch, fn, frames, live, cursor, operands, height, offsets, depths⟩
          cases result with
          | Err error =>
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
            obtain ⟨rfl, rfl⟩ := tail
            exact .rejected loopCall
          | Ok unitValue =>
            cases unitValue
            refine EndLoopEffect.published (middle := current) ?_ ?_
            · exact loopCall
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
            obtain ⟨⟨map, restore⟩, read, tail⟩ := bind_ok_inv _ _ _ tail
            simp only [uncurry_apply_pair] at tail
            obtain ⟨targetIndex, cast, tail⟩ := bind_ok_inv _ _ _ tail
            obtain ⟨source, added, tail⟩ := bind_ok_inv _ _ _ tail
            refine ⟨map, restore, targetIndex, source, read, cast, added, ?_⟩
            cases liveEq : live <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
              simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair] at tail
            all_goals first
              | apply EndFinish.nested (by rw [kindEq]; intro impossible; cases impossible)
                simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or] using tail
              | obtain ⟨⟨answer, emitted⟩, emitCall, tail⟩ := bind_ok_inv _ _ _ tail
                cases answer with
                | Err error =>
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
                  obtain ⟨rfl, rfl⟩ := tail
                  apply EndFinish.returnRejected kindEq
                  simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true] using emitCall
                | Ok unitValue =>
                  cases unitValue
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
                  apply EndFinish.returned kindEq _ tail
                  simpa only [endPublished, endReachable, current, liveEq, endsEq, kindEq, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true] using emitCall


/-- Checked closure inputs shared by the normal-result end contract. -/
structure EndTotalInputs {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) where
  frame : runtime.compiler.Frame
  remaining : alloc.vec.Vec runtime.compiler.Frame
  frames : before.frames.val = remaining.val ++ [frame]
  branches : BranchSites before.function.code.val frame.fixups.val
  guardSites : ∀ guard, frame.if_pc = some guard →
    ∃ branch old, before.function.code.val[guard.val]? = some (BranchKind.instruction branch old)
  mapFits : frame.map.val < before.function.controls.val.length
  coordinateFits : before.function.body_start.val + state.pos.val ≤ Usize.max
  space : frame.kind = .Body → before.function.code.length < Usize.max ∧
    before.function.source_offsets.length < Usize.max ∧
    before.function.body_start.val + before.next_source.val ≤ Usize.max

/-- Capacity and frame facts needed by available end callbacks. -/
structure EndAvailableInputs {A : Type} (bound : Nat) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) where
  frame : runtime.compiler.Frame
  remaining : alloc.vec.Vec runtime.compiler.Frame
  frames : before.frames.val = remaining.val ++ [frame]
  branches : BranchSites before.function.code.val frame.fixups.val
  guardSites : ∀ guard, frame.if_pc = some guard →
    ∃ branch old, before.function.code.val[guard.val]? = some (BranchKind.instruction branch old)
  mapFits : frame.map.val < before.function.controls.val.length
  coordinateFits : before.function.body_start.val + state.pos.val ≤ Usize.max
  pcFits : before.function.code.length ≤ U32.max
  request : state.vals.length ≤ bound
  slotsFit : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max
  space : frame.kind = .Body → before.function.code.length < Usize.max ∧
    before.function.source_offsets.length < Usize.max ∧
    before.function.body_start.val + before.next_source.val ≤ Usize.max ∧
    before.function.code.length + 1 ≤ bound ∧ before.function.source_offsets.length + 1 ≤ bound ∧
    before.budget.instructions.val < before.budget.limits.max_instructions.val


/-- Safe frame/map selection and branch sites make closure normal. Only a root
frame needs the numeric capacity for its final return instruction. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (inputs : EndTotalInputs before state) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt ⦃ _ => True ⦄ := by
  rcases inputs with ⟨frame, remaining, frames, branches, guardSites, mapFits, coordinateFits, space⟩
  have pop : alloc.vec.Vec.pop Global before.frames = .ok (some frame, remaining) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.from_val]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  rw [pop]
  simp only [bind_ok, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  step with compiler_pc ops {before with frames := remaining} as ⟨answer, counted, functionEq, targetEq, budget, countedEq⟩
  cases answer with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok target =>
    subst counted
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let popped := {before with frames := remaining, budget := budget}
    cases guardEq : frame.if_pc with
    | none =>
      step with compiler_fixups ops popped frame.fixups target 0#usize (by exact Nat.zero_le _)
        (show BranchSites popped.function.code.val frame.fixups.val from branches)
        as ⟨s, slots, budget1, batch, fn, frames1, live, cursor, operands, height, offsets, depths, status,
          current, snapshot, onlyCode, patched⟩
      simp only [compilerSnapshot, Prod.mk.injEq] at snapshot
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := snapshot
      obtain ⟨code, rfl⟩ := onlyCode
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨map, restore, read, restored⟩
      step as ⟨targetIndex, cast⟩
      step as ⟨source, added⟩
      cases liveEq : before.reachable <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
        simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair]
      all_goals first
        | exact WP.spec_mono (compiler_observe ops law _ state) (fun _ _ => trivial)
        | have codeLength : code.length = before.function.code.length := by
            simp only [alloc.vec.Vec.length, patched, List.drop_zero, patch_code_length]
          obtain ⟨codeFits, sourcesFit, coordinate⟩ := space kindEq
          have fits : code.length < Usize.max := by rw [codeLength]; exact codeFits
          step with compiler_emit ops law as ⟨answer, emitted, effect⟩
          cases answer with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          | Ok unitValue =>
            cases unitValue
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact WP.spec_mono (compiler_observe ops law emitted state) (fun _ _ => trivial)
    | some guard =>
      obtain ⟨branch, old, site⟩ := guardSites guard guardEq
      step with runtime.compiler.control.FunctionCompiler.patch.available ops popped guard branch old target
        (show popped.function.code.val[guard.val]? = some (branch.instruction old) from site)
        as ⟨answer, patchedCompiler, accepted, patchEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have patchedBranches := patchEffect.branch_sites (List.getElem?_eq_some_iff.mp site).1 branches
      obtain ⟨guardCode, rfl, guardSet⟩ := patchEffect
      step with compiler_fixups_after_if ops _ frame.fixups target 0#usize (by exact Nat.zero_le _) patchedBranches
        as ⟨s, slots, budget1, batch, fn, frames1, live, cursor, operands, height, offsets, depths, status,
          current, snapshot, onlyCode, patched⟩
      simp only [compilerSnapshot, Prod.mk.injEq] at snapshot
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := snapshot
      obtain ⟨code, rfl⟩ := onlyCode
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨map, restore, read, restored⟩
      step as ⟨targetIndex, cast⟩
      step as ⟨source, added⟩
      cases liveEq : before.reachable <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
        simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair]
      all_goals first
        | exact WP.spec_mono (compiler_observe ops law _ state) (fun _ _ => trivial)
        | have codeLength : code.length = before.function.code.length := by
            simp only [alloc.vec.Vec.length, patched, List.drop_zero, patch_code_length, guardSet, List.length_set]
          obtain ⟨codeFits, sourcesFit, coordinate⟩ := space kindEq
          have fits : code.length < Usize.max := by rw [codeLength]; exact codeFits
          step with compiler_emit ops law as ⟨answer, emitted, effect⟩
          cases answer with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          | Ok unitValue =>
            cases unitValue
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact WP.spec_mono (compiler_observe ops law emitted state) (fun _ _ => trivial)

/-- Available allocation accepts a safe closure and charges exactly one instruction
for a root frame, leaving every other budget component unchanged. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (inputs : EndAvailableInputs bound before state) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (match inputs.frame.kind with | .Body => 1 | _ => 0) ⦄ := by
  rcases inputs with ⟨frame, remaining, frames, branches, guardSites, mapFits, coordinateFits, pcFits, request, slotsFit, space⟩
  have pop : alloc.vec.Vec.pop Global before.frames = .ok (some frame, remaining) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.from_val]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  rw [pop]
  simp only [bind_ok, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  step with compiler_pc_available ops {before with frames := remaining} pcFits
    as ⟨answer, counted, countedEq, target, accepted, targetEq⟩
  subst counted
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  let popped := {before with frames := remaining}
  cases guardEq : frame.if_pc with
  | none =>
    step with compiler_fixups ops popped frame.fixups target 0#usize (by exact Nat.zero_le _)
      (show BranchSites popped.function.code.val frame.fixups.val from branches)
      as ⟨s, slots, budget1, batch, fn, frames1, live, cursor, operands, height, offsets, depths, status,
        current, snapshot, onlyCode, patched⟩
    simp only [compilerSnapshot, Prod.mk.injEq] at snapshot
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := snapshot
    obtain ⟨code, rfl⟩ := onlyCode
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨map, restore, read, restored⟩
    step as ⟨targetIndex, cast⟩
    step as ⟨source, added⟩
    cases liveEq : before.reachable <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
      simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair]
    all_goals first
      | step with compiler_observe_available_budget ops bound available as ⟨status, after, accepted, kept⟩
        refine ⟨accepted, before.budget.instructions, ?_, ?_⟩
        · simpa only using kept
        · simp only [Nat.add_zero]
      | have codeLength : code.length = before.function.code.length := by
          simp only [alloc.vec.Vec.length, patched, List.drop_zero, patch_code_length]
        obtain ⟨codeFits, sourcesFit, coordinate, codeRequest, sourceRequest, room⟩ := space kindEq
        have fits : code.length < Usize.max := by rw [codeLength]; exact codeFits
        have pcBound : code.length ≤ U32.max := by rw [codeLength]; exact pcFits
        have codeReserve : code.length + 1 ≤ bound := by rw [codeLength]; exact codeRequest
        step with runtime.compiler.FunctionCompiler.emit.available ops bound available
          as ⟨answer, emitted, accepted, effect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨used, emittedCode, sources, emittedEq, usedEq, _, _⟩ := effect
        have locals : emitted.function.local_slots = before.function.local_slots := by rw [emittedEq]
        apply WP.spec_mono (compiler_observe_available_budget ops bound available emitted state request
          (by rw [locals]; exact slotsFit))
        rintro ⟨status, after⟩ ⟨accepted, kept⟩
        refine ⟨accepted, used, ?_, ?_⟩
        · rw [kept, emittedEq]
        · simpa only [kindEq] using usedEq
  | some guard =>
    obtain ⟨branch, old, site⟩ := guardSites guard guardEq
    step with runtime.compiler.control.FunctionCompiler.patch.available ops popped guard branch old target
      (show popped.function.code.val[guard.val]? = some (branch.instruction old) from site)
      as ⟨answer, patchedCompiler, accepted, patchEffect⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have patchedBranches := patchEffect.branch_sites (List.getElem?_eq_some_iff.mp site).1 branches
    obtain ⟨guardCode, rfl, guardSet⟩ := patchEffect
    step with compiler_fixups_after_if ops _ frame.fixups target 0#usize (by exact Nat.zero_le _) patchedBranches
      as ⟨s, slots, budget1, batch, fn, frames1, live, cursor, operands, height, offsets, depths, status,
        current, snapshot, onlyCode, patched⟩
    simp only [compilerSnapshot, Prod.mk.injEq] at snapshot
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := snapshot
    obtain ⟨code, rfl⟩ := onlyCode
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨map, restore, read, restored⟩
    step as ⟨targetIndex, cast⟩
    step as ⟨source, added⟩
    cases liveEq : before.reachable <;> cases endsEq : frame.end_reachable <;> cases kindEq : frame.kind <;>
      simp only [liveEq, endsEq, kindEq, Bool.false_eq_true, ite_false, ite_true, bind_ok, uncurry_apply_pair]
    all_goals first
      | step with compiler_observe_available_budget ops bound available as ⟨status, after, accepted, kept⟩
        refine ⟨accepted, before.budget.instructions, ?_, ?_⟩
        · simpa only using kept
        · simp only [Nat.add_zero]
      | have codeLength : code.length = before.function.code.length := by
          simp only [alloc.vec.Vec.length, patched, List.drop_zero, patch_code_length, guardSet, List.length_set]
        obtain ⟨codeFits, sourcesFit, coordinate, codeRequest, sourceRequest, room⟩ := space kindEq
        have fits : code.length < Usize.max := by rw [codeLength]; exact codeFits
        have pcBound : code.length ≤ U32.max := by rw [codeLength]; exact pcFits
        have codeReserve : code.length + 1 ≤ bound := by rw [codeLength]; exact codeRequest
        step with runtime.compiler.FunctionCompiler.emit.available ops bound available
          as ⟨answer, emitted, accepted, effect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨used, emittedCode, sources, emittedEq, usedEq, _, _⟩ := effect
        have locals : emitted.function.local_slots = before.function.local_slots := by rw [emittedEq]
        apply WP.spec_mono (compiler_observe_available_budget ops bound available emitted state request
          (by rw [locals]; exact slotsFit))
        rintro ⟨status, after⟩ ⟨accepted, kept⟩
        refine ⟨accepted, used, ?_, ?_⟩
        · rw [kept, emittedEq]
        · simpa only [kindEq] using usedEq

def EndFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with budget := after.budget, before := after.before, height := after.height, next_source := after.next_source, frames := after.frames, reachable := after.reachable, function := {before.function with code := after.function.code, source_offsets := after.function.source_offsets, max_stack := after.function.max_stack, slot_count := after.function.slot_count, controls := after.function.controls}}

theorem EndFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : EndFrame before middle) (second : EndFrame middle after) : EndFrame before after := by
  unfold EndFrame at *
  rw [second, first]

/-- One traversal records immutable fields and map size without allocator laws;
only slot monotonicity uses allocator correctness. -/
structure EndSummary {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) : Prop where
  frame : EndFrame before after
  maps : after.function.controls.val.length = before.function.controls.val.length
  slots : Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val

theorem EndSummary.trans {A : Type} {ops : runtime.platform.Alloc A}
    {before middle after : runtime.compiler.FunctionCompiler A}
    (first : EndSummary ops before middle) (second : EndSummary ops middle after) :
    EndSummary ops before after :=
  ⟨first.frame.trans second.frame, second.maps.trans first.maps,
    fun law => (first.slots law).trans (second.slots law)⟩

private theorem end_pc_summary {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (status)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    EndSummary ops before after := by
  have post := compiler_pc ops before
  rw [called, WP.spec_ok] at post
  obtain ⟨_, _, budget, same⟩ := post
  change after = {before with budget} at same
  rw [same]
  exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem end_patch_summary {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32) (status)
    (called : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    EndSummary ops before after := by
  rcases compiler_patch_cases ops before after pc target status called with rfl | ⟨instruction, code, rfl, _⟩
  all_goals exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem end_emit_summary {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr) (status)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    EndSummary ops before after := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status called).1
  change after = _ at frame
  rw [frame]
  exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

private theorem end_observe_summary {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (status)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    EndSummary ops before after := by
  have frame := compiler_observe_frame_raw ops before state status after called
  refine ⟨?_, ?_, fun law => ?_⟩
  · unfold EndFrame
    rw [frame]
  · rw [frame]
  · have post := compiler_observe_inv ops law before state
    rw [called, WP.spec_ok] at post
    exact post.2

private theorem end_loop_summary {A : Type} {ops : runtime.platform.Alloc A} {guarded : Bool}
    {before after : runtime.compiler.FunctionCompiler A} {sites target status}
    (called : EndLoopCall ops guarded before sites target status after) : EndSummary ops before after := by
  have fields : OnlyCode before after := by
    cases guarded <;> exact compiler_fixups_frame ops before sites target 0#usize (.Ok ()) (compilerSnapshot after status) called
  obtain ⟨code, rfl⟩ := fields
  exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

theorem EndFinish.summary {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndFinish ops state frame before status after) : EndSummary ops before after := by
  cases effect with
  | nested nonBody observed => exact end_observe_summary ops _ _ _ _ observed
  | returnRejected body emitted => exact end_emit_summary ops _ _ _ _ emitted
  | returned body emitted observed => exact (end_emit_summary ops _ _ _ _ emitted).trans (end_observe_summary ops _ _ _ _ observed)

theorem EndPublication.summary {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndPublication ops state frame target before status after) : EndSummary ops before after := by
  obtain ⟨map, restore, targetIndex, source, read, _, _, finished⟩ := effect
  have published : EndSummary ops before (endPublished before frame map restore targetIndex source) := by
    refine ⟨rfl, ?_, fun _ => Nat.le_refl _⟩
    rw [alloc.vec.Vec.index_mut_slice_index] at read
    unfold alloc.vec.Vec.index_mut_usize at read
    obtain ⟨found, _, read⟩ := bind_ok_inv _ _ _ read
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Result.ok.injEq.mp read)
    simp only [endPublished, alloc.vec.Vec.set_val_eq, List.length_set]
  exact published.trans finished.summary

theorem EndLoopEffect.summary {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {guarded : Bool}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndLoopEffect ops state frame target guarded before status after) : EndSummary ops before after := by
  cases effect with
  | rejected called => exact end_loop_summary called
  | published called publication => exact (end_loop_summary called).trans publication.summary

theorem EndGuardEffect.summary {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndGuardEffect ops state frame target before status after) : EndSummary ops before after := by
  cases effect with
  | unguarded guard loop => exact loop.summary
  | rejected selected patched => exact end_patch_summary ops _ _ _ _ _ patched
  | guarded selected patched loop => exact (end_patch_summary ops _ _ _ _ _ patched).trans loop.summary

theorem EndEffect.summary {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndEffect ops state before status after) : EndSummary ops before after := by
  cases effect with
  | empty popped => exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩
  | @pcRejected frame frames error after popped counted =>
    exact (show EndSummary ops before {before with frames} from ⟨rfl, rfl, fun _ => Nat.le_refl _⟩).trans (end_pc_summary ops _ _ _ counted)
  | @counted frame frames target middle status after popped count guard =>
    exact ((show EndSummary ops before {before with frames} from ⟨rfl, rfl, fun _ => Nat.le_refl _⟩).trans (end_pc_summary ops _ _ _ count)).trans guard.summary

theorem EndEffect.frame {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndEffect ops state before status after) : EndFrame before after := by
  exact effect.summary.frame

theorem EndEffect.capacity {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndEffect ops state before status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  exact effect.summary.slots law

/-- Both fixup loops retain all compiler fields except the instruction vector. -/
theorem EndLoopCall.only_code {A : Type} {ops : runtime.platform.Alloc A} {guarded : Bool}
    {before after : runtime.compiler.FunctionCompiler A} {sites : alloc.vec.Vec Usize} {target : U32} {status}
    (called : EndLoopCall ops guarded before sites target status after) : OnlyCode before after := by
  have actual : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 ops before sites target 0#usize (.Ok ()) =
      .ok (compilerSnapshot after status) := by
    cases guarded <;> exact called
  have fields := compiler_fixups_frame ops before sites target 0#usize (.Ok ()) (compilerSnapshot after status) actual
  exact fields

theorem EndLoopCall.code_length {A : Type} {ops : runtime.platform.Alloc A} {guarded : Bool}
    {before after : runtime.compiler.FunctionCompiler A} {sites : alloc.vec.Vec Usize} {target : U32} {status}
    (called : EndLoopCall ops guarded before sites target status after) :
    after.function.code.val.length = before.function.code.val.length := by
  have actual : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 ops before sites target 0#usize (.Ok ()) =
      .ok (compilerSnapshot after status) := by
    cases guarded <;> exact called
  exact compiler_fixups_code_length ops before sites target 0#usize (.Ok ()) (compilerSnapshot after status) actual

theorem EndLoopEffect.before_publication {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {guarded : Bool} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndLoopEffect ops state frame target guarded before (.Ok ()) after) :
    ∃ middle, OnlyCode before middle ∧ middle.function.code.val.length = before.function.code.val.length ∧ EndPublication ops state frame target middle (.Ok ()) after := by
  cases effect with
  | published called publication => exact ⟨_, called.only_code, called.code_length, publication⟩

theorem EndGuardEffect.before_publication {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndGuardEffect ops state frame target before (.Ok ()) after) :
    ∃ middle, OnlyCode before middle ∧ middle.function.code.val.length = before.function.code.val.length ∧ EndPublication ops state frame target middle (.Ok ()) after := by
  cases effect with
  | unguarded guard loop => exact loop.before_publication
  | @guarded guard patchedState status after selected patched loop =>
    obtain ⟨middle, onlyCode, length, publication⟩ := loop.before_publication
    have patchFrame : OnlyCode before patchedState := by
      rcases compiler_patch_cases ops _ _ _ _ _ patched with same | ⟨instruction, code, same, codeEq⟩
      · rw [same]; exact .refl _
      · exact ⟨code, same⟩
    refine ⟨middle, patchFrame.trans onlyCode, ?_, publication⟩
    have patchLength : patchedState.function.code.val.length = before.function.code.val.length := by
        rcases compiler_patch_cases ops _ _ _ _ _ patched with same | ⟨instruction, code, same, codeEq⟩
        · rw [same]
        · rw [same]
          change code.val.length = _
          rw [codeEq, List.length_set]
    exact length.trans patchLength

/-- The selected frame is popped before any successful close publication. -/
theorem EndEffect.before_publication {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) :
    ∃ frame remaining target budget middle,
      alloc.vec.Vec.pop Global before.frames = .ok (some frame, remaining) ∧
      OnlyCode {before with frames := remaining, budget} middle ∧
      middle.function.code.val.length = before.function.code.val.length ∧
      EndPublication ops state frame target middle (.Ok ()) after := by
  cases effect with
  | @counted frame remaining target counted status after popped count guarded =>
    obtain ⟨middle, onlyCode, length, publication⟩ := guarded.before_publication
    have post := compiler_pc ops {before with frames := remaining}
    rw [count, WP.spec_ok] at post
    obtain ⟨_, _, budget, same⟩ := post
    dsimp only at same
    rw [same] at onlyCode length
    exact ⟨_, _, _, budget, middle, popped, onlyCode, length, publication⟩

theorem EndFinish.observation {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndFinish ops state frame before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | nested nonBody observed => exact ⟨_, observed⟩
  | returned body emitted observed => exact ⟨_, observed⟩

theorem EndEffect.observation {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  obtain ⟨frame, remaining, target, budget, middle, popped, retained, length, publication⟩ := effect.before_publication
  obtain ⟨map, restore, targetIndex, source, read, cast, added, finished⟩ := publication
  exact finished.observation

/-- Successful finalization preserves published frames/maps and appends exactly
the implicit return instruction for a function body. -/
theorem EndFinish.success_fields {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndFinish ops state frame before (.Ok ()) after) (law : Platform.AllocCorrect ops) :
    after.frames = before.frames ∧ after.reachable = before.reachable ∧
    after.function.controls = before.function.controls ∧
    after.function.code.val = before.function.code.val ++ (match frame.kind with
      | .Body => [.Return frame.height (if before.reachable then frame.results else 0#u32)] | _ => []) ∧
    after.function.source_offsets.val.map UScalar.val = before.function.source_offsets.val.map UScalar.val ++
      (match frame.kind with | .Body => [before.function.body_start.val + before.next_source.val] | _ => []) := by
  cases effect with
  | nested nonBody observed =>
    have unchanged := compiler_observe_frame_raw ops _ _ _ _ observed
    rw [unchanged]
    cases kindEq : frame.kind <;> simp only [kindEq] at nonBody ⊢
    all_goals first | exact False.elim (nonBody rfl) | exact ⟨True.intro, True.intro, True.intro, (List.append_nil _).symm, (List.append_nil _).symm⟩
  | returned body emitted observed =>
    have unchanged := compiler_observe_frame_raw ops _ _ _ _ observed
    have exactEmit := (runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ emitted).2 law |>.2 rfl
    obtain ⟨used, code, sources, emittedEq, _, codeAppend, sourceAppend⟩ := exactEmit
    rw [unchanged, emittedEq]
    exact ⟨rfl, rfl, rfl, by simpa only [body] using codeAppend, by simpa only [body] using sourceAppend⟩

/-- The successful optional epilogue does not alter the slot bounds before observation. -/
theorem EndFinish.observation_slots {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndFinish ops state frame before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) ∧
      middle.function.slot_count = before.function.slot_count ∧ middle.function.local_slots = before.function.local_slots := by
  cases effect with
  | nested nonBody observed => exact ⟨_, observed, rfl, rfl⟩
  | returned body emitted observed =>
    have unchanged := (runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ emitted).1
    refine ⟨_, observed, ?_, ?_⟩ <;> rw [unchanged]

/-- The closed map retains its entry coordinates and records the checked end
coordinates; a root body additionally publishes its implicit return. -/
theorem EndPublication.success_fields {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndPublication ops state frame target before (.Ok ()) after) (law : Platform.AllocCorrect ops)
    (mapFits : frame.map.val < before.function.controls.val.length) :
    after.frames = before.frames ∧ after.reachable = endReachable before.reachable frame ∧
    after.function.code.val = before.function.code.val ++ (match frame.kind with
      | .Body => [.Return frame.height (if endReachable before.reachable frame then frame.results else 0#u32)] | _ => []) ∧
    ∃ original closed, before.function.controls.val[frame.map.val]? = some original ∧
      after.function.controls.val = before.function.controls.val.set frame.map.val closed ∧
      closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
      closed.end_pc.val = target.val ∧ closed.source_end.val = before.function.body_start.val + state.pos.val := by
  obtain ⟨map, restore, targetIndex, source, read, cast, added, finished⟩ := effect
  have selected := alloc.vec.Vec.index_mut_usize_spec before.function.controls frame.map mapFits
  rw [← alloc.vec.Vec.index_mut_slice_index, read, WP.spec_ok] at selected
  obtain ⟨mapEq, restoreEq⟩ := selected
  have targetVal : targetIndex.val = target.val := by
    have pure := Result.ok_injective cast
    rw [← pure]
    scalar_tac
  have sum := UScalar.add_equiv before.function.body_start state.pos
  rw [added] at sum
  have sourceVal : source.val = before.function.body_start.val + state.pos.val := sum.2.1
  obtain ⟨frames, reachable, controls, code, sources⟩ := finished.success_fields law
  refine ⟨frames, reachable, code, map, {map with source_end := source, end_pc := targetIndex}, ?_, ?_, rfl, rfl, targetVal, sourceVal⟩
  · rw [mapEq]
    exact List.getElem?_eq_getElem mapFits
  · rw [controls]
    change (restore _).val = _
    rw [restoreEq, alloc.vec.Vec.set_val_eq]

theorem EndEffect.last_frame {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after)
    (frame : runtime.compiler.Frame) (remaining : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : before.frames.val = remaining.val ++ [frame])
    (position : target.val = before.function.code.val.length) :
    ∃ budget, EndGuardEffect ops state frame target {before with frames := remaining, budget} (.Ok ()) after := by
  have pop : alloc.vec.Vec.pop Global before.frames = .ok (some frame, remaining) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.from_val]
  cases effect with
  | @counted selected rest actual counted status after popped count finished =>
    rw [pop, Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at popped
    obtain ⟨rfl, rfl⟩ := popped
    have post := compiler_pc ops {before with frames := remaining}
    rw [count, WP.spec_ok] at post
    obtain ⟨_, targetEq, budget, same⟩ := post
    dsimp only at targetEq same
    have targetSame : actual = target := by
      apply UScalar.eq_of_val_eq
      exact (targetEq actual rfl).trans position.symm
    subst actual
    rw [same] at finished
    exact ⟨budget, finished⟩

/-- Owned branch sites give the exact list patch performed by either generated loop. -/
theorem EndLoopCall.success {A : Type} {ops : runtime.platform.Alloc A} {guarded : Bool}
    {before after : runtime.compiler.FunctionCompiler A} {sites : alloc.vec.Vec Usize} {target : U32}
    (called : EndLoopCall ops guarded before sites target (.Ok ()) after)
    (branches : BranchSites before.function.code.val sites.val) :
    OnlyCode before after ∧ after.function.code.val = patchCode before.function.code.val sites.val target := by
  have post := compiler_fixups ops before sites target 0#usize (Nat.zero_le _) branches
  have actual : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 ops before sites target 0#usize (.Ok ()) =
      .ok (compilerSnapshot after (.Ok ())) := by
    cases guarded <;> exact called
  rw [actual, WP.spec_ok] at post
  obtain ⟨found, snapshot, onlyCode, exactCode⟩ := post
  have same := congrArg snapshotCompiler snapshot
  dsimp only [snapshotCompiler, compilerSnapshot] at same
  change after = found at same
  subst found
  exact ⟨onlyCode, by simpa only [show (0#usize).val = 0 from rfl, List.drop_zero] using exactCode⟩

theorem EndGuardEffect.unguarded_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndGuardEffect ops state frame target before (.Ok ()) after)
    (noGuard : frame.if_pc = none) (branches : BranchSites before.function.code.val frame.fixups.val) :
    ∃ middle, OnlyCode before middle ∧ middle.function.code.val = patchCode before.function.code.val frame.fixups.val target ∧
      EndPublication ops state frame target middle (.Ok ()) after := by
  cases effect with
  | unguarded guard loop =>
    cases loop with
    | published called publication =>
      obtain ⟨onlyCode, code⟩ := called.success branches
      exact ⟨_, onlyCode, code, publication⟩
  | guarded selected patched loop => rw [noGuard] at selected; cases selected

theorem EndGuardEffect.guarded_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {frame : runtime.compiler.Frame} {target : U32} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndGuardEffect ops state frame target before (.Ok ()) after)
    (guard : Usize) (condition old : U32) (guardPc : frame.if_pc = some guard)
    (site : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : BranchSites before.function.code.val frame.fixups.val) :
    ∃ middle, OnlyCode before middle ∧
      middle.function.code.val = patchCode (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target ∧
      EndPublication ops state frame target middle (.Ok ()) after := by
  cases effect with
  | unguarded selected loop => rw [guardPc] at selected; cases selected
  | @guarded actual patched status after selected patchCall loop =>
    have guardSame : actual = guard := Option.some.inj (selected.symm.trans guardPc)
    subst actual
    have post := runtime.compiler.control.FunctionCompiler.patch.available ops before guard (.zero condition) old target site
    rw [patchCall, WP.spec_ok] at post
    obtain ⟨_, patchEffect⟩ := post
    dsimp only at patchEffect
    have nextBranches := patchEffect.branch_sites (List.getElem?_eq_some_iff.mp site).1 branches
    cases loop with
    | published called publication =>
      obtain ⟨onlyCode, exactCode⟩ := called.success nextBranches
      refine ⟨_, patchEffect.only_code.trans onlyCode, ?_, publication⟩
      obtain ⟨code, patchedEq, codeEq⟩ := patchEffect
      simpa only [patchedEq, codeEq, BranchKind.instruction] using exactCode

/-- Exact successful close effect, including the selected map's original entry. -/
theorem EndEffect.unguarded_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) (law : Platform.AllocCorrect ops)
    (frame : runtime.compiler.Frame) (remaining : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : before.frames.val = remaining.val ++ [frame])
    (position : target.val = before.function.code.val.length)
    (noGuard : frame.if_pc = none)
    (branches : BranchSites before.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < before.function.controls.val.length) :
    after.frames = remaining ∧ after.reachable = endReachable before.reachable frame ∧
    after.function.code.val = patchCode before.function.code.val frame.fixups.val target ++ (match frame.kind with
      | .Body => [.Return frame.height (if endReachable before.reachable frame then frame.results else 0#u32)] | _ => []) ∧
    ∃ original closed, before.function.controls.val[frame.map.val]? = some original ∧
      after.function.controls.val = before.function.controls.val.set frame.map.val closed ∧
      closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
      closed.end_pc.val = target.val ∧ closed.source_end.val = before.function.body_start.val + state.pos.val := by
  obtain ⟨budget, guarded⟩ := effect.last_frame frame remaining target frames position
  obtain ⟨middle, onlyCode, patched, publication⟩ := guarded.unguarded_success noGuard branches
  obtain ⟨code, rfl⟩ := onlyCode
  have fields := publication.success_fields law mapFits
  dsimp only at fields patched
  rw [patched] at fields
  exact fields


/-- Frame, guard, and map premises for the successful guarded end projection. -/
structure EndGuardedSuccessInputs {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) where
  frame : runtime.compiler.Frame
  remaining : alloc.vec.Vec runtime.compiler.Frame
  target : U32
  frames : before.frames.val = remaining.val ++ [frame]
  position : target.val = before.function.code.val.length
  guard : Usize
  condition : U32
  old : U32
  guardPc : frame.if_pc = some guard
  site : before.function.code.val[guard.val]? = some (.JumpIfZero condition old)
  branches : BranchSites before.function.code.val frame.fixups.val
  mapFits : frame.map.val < before.function.controls.val.length

/-- Exact successful close effect, including the selected map's original entry. -/
theorem EndEffect.guarded_success {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) (law : Platform.AllocCorrect ops)
    (inputs : EndGuardedSuccessInputs before state) :
    after.frames = inputs.remaining ∧ after.reachable = endReachable before.reachable inputs.frame ∧
    after.function.code.val = patchCode (before.function.code.val.set inputs.guard.val
      (.JumpIfZero inputs.condition inputs.target)) inputs.frame.fixups.val inputs.target ++
      (match inputs.frame.kind with | .Body => [.Return inputs.frame.height
        (if endReachable before.reachable inputs.frame then inputs.frame.results else 0#u32)] | _ => []) ∧
    ∃ original closed, before.function.controls.val[inputs.frame.map.val]? = some original ∧
      after.function.controls.val = before.function.controls.val.set inputs.frame.map.val closed ∧
      closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
      closed.end_pc.val = inputs.target.val ∧ closed.source_end.val = before.function.body_start.val + state.pos.val := by
  rcases inputs with ⟨frame, remaining, target, frames, position, guard, condition, old, guardPc, site, branches, mapFits⟩
  obtain ⟨budget, guarded⟩ := effect.last_frame frame remaining target frames position
  obtain ⟨middle, onlyCode, patched, publication⟩ := guarded.guarded_success guard condition old guardPc site branches
  obtain ⟨code, rfl⟩ := onlyCode
  have fields := publication.success_fields law mapFits
  dsimp only at fields patched
  rw [patched] at fields
  exact fields

theorem EndEffect.observation_slots {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) ∧
      middle.function.slot_count = before.function.slot_count ∧ middle.function.local_slots = before.function.local_slots := by
  obtain ⟨frame, remaining, target, budget, compiler, popped, onlyCode, length, publication⟩ := effect.before_publication
  obtain ⟨code, rfl⟩ := onlyCode
  obtain ⟨map, restore, targetIndex, source, read, cast, added, finished⟩ := publication
  obtain ⟨middle, observed, slots, locals⟩ := finished.observation_slots
  exact ⟨middle, observed, slots, locals⟩

/-- Success retains the popped frame stack and appends a source origin only for
an implicit function return, independently of branch-site hypotheses. -/
theorem EndEffect.sources_frames {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : EndEffect ops state before (.Ok ()) after) (law : Platform.AllocCorrect ops) :
    ∃ frame remaining, alloc.vec.Vec.pop Global before.frames = .ok (some frame, remaining) ∧
      after.frames = remaining ∧
      after.function.code.val.length = before.function.code.val.length + (match frame.kind with | .Body => 1 | _ => 0) ∧
      after.function.source_offsets.val.map UScalar.val = before.function.source_offsets.val.map UScalar.val ++
        (match frame.kind with | .Body => [before.function.body_start.val + before.next_source.val] | _ => []) := by
  obtain ⟨frame, remaining, target, budget, compiler, popped, onlyCode, length, publication⟩ := effect.before_publication
  obtain ⟨code, rfl⟩ := onlyCode
  obtain ⟨map, restore, targetIndex, source, read, cast, added, finished⟩ := publication
  obtain ⟨frames, reachable, controls, code, sources⟩ := finished.success_fields law
  refine ⟨frame, remaining, popped, frames, ?_, sources⟩
  rw [code, List.length_append]
  dsimp only [endPublished] at length ⊢
  rw [length]
  cases frame.kind <;> rfl

theorem EndEffect.map_count {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : EndEffect ops state before status after) :
    after.function.controls.val.length = before.function.controls.val.length := by
  exact effect.summary.maps

end Itasca.Runtime.Compiler
