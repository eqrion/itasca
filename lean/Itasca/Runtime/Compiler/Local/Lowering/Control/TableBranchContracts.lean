import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra

/-! Canonical contracts for publishing table targets and lowering the target loop.
Operational traces retain intermediate states without allocator assumptions. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- One target records its current PC, publishes that PC in the side table,
then lowers the selected branch. Ordinary errors retain their actual state. -/
def TableBranchEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ answer current, runtime.compiler.FunctionCompiler.pc ops before = .ok (answer, current) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = current
    | .Ok target => ∃ pushed budget table,
      runtime.compiler.Budget.push ops current.budget current.function.jump_tables target = .ok (pushed, budget, table) ∧
      let staged := {current with budget, function := {current.function with jump_tables := table}}
      match pushed with
      | .Err error => status = .Err error ∧ after = staged
      | .Ok _ => ∃ depth,
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) current.table_depths index = .ok depth ∧
        runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (status, after)

/-- Inversion records all three stages, including ordinary-error exits. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    TableBranchEffect ops before after index status := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at called
  obtain ⟨⟨answer, current⟩, pc, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨answer, current, pc, ?_⟩
  cases answer with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | Ok target =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨answer, budget, table⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨answer, budget, table, pushed, ?_⟩
    cases answer with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨depth, selected, branch⟩ := bind_ok_inv _ _ _ rest
      exact ⟨depth, selected, branch⟩

/-- Normality composes representable table publication with the branch's
normality certificate for every allocation-accounting outcome. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (tableFits : before.function.jump_tables.val.length < Usize.max)
    (branchReady : ∀ budget table, runtime.compiler.control.FunctionCompiler.branch ops
      {before with budget, function := {before.function with jump_tables := table}}
      depth 1#u32 false ⦃ _ => True ⦄) :
    runtime.compiler.control.FunctionCompiler.table_branch ops before index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc ops before as ⟨answer, current, _, _, budget, same⟩
  subst current
  cases answer with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok target =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law budget before.function.jump_tables target tableFits as
      ⟨answer, budget, table, _⟩
    cases answer with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have inside := (List.getElem?_eq_some_iff.mp lookup).1
      step as ⟨actual, found⟩
      have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp lookup).2
      subst actual
      rw [(List.getElem?_eq_some_iff.mp lookup).2]
      exact branchReady budget table

/-- Available publication leaves the instruction budget untouched before the
branch; the child certificate describes its exact successful result. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (pcFits : before.function.code.val.length ≤ U32.max)
    (tableFits : before.function.jump_tables.length < Usize.max)
    (tableReserve : before.function.jump_tables.length + 1 ≤ bound)
    (post : runtime.compiler.FunctionCompiler A → Prop)
    (branchReady : ∀ table, runtime.compiler.control.FunctionCompiler.branch ops
      {before with function := {before.function with jump_tables := table}}
      depth 1#u32 false ⦃ (status, after) => status = .Ok () ∧ post after ⦄) :
    runtime.compiler.control.FunctionCompiler.table_branch ops before index
      ⦃ (status, after) => status = .Ok () ∧ post after ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc_available ops before pcFits as ⟨answer, current, same, target, accepted, _⟩
  subst current
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available before.budget before.function.jump_tables target
    tableFits tableReserve as ⟨answer, budget, table, accepted, same, _⟩
  subst answer budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual, found⟩
  have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp lookup).2
  subst actual
  rw [(List.getElem?_eq_some_iff.mp lookup).2]
  exact branchReady table

/-- The final Rust status in an extracted compiler snapshot. -/
def snapshotStatus {A : Type} (output : CompilerSnapshot A) :
    core.result.Result Unit Itasca.error.VisitError :=
  let (_, _, _, _, _, _, _, _, _, _, _, _, result) := output
  result

/-- A finite table-target traversal, retaining failures as well as success. -/
inductive TableLoopEffect {A : Type} (ops : runtime.platform.Alloc A) :
    runtime.compiler.FunctionCompiler A → Nat → core.result.Result Unit Itasca.error.VisitError →
      CompilerSnapshot A → Prop where
  | done (before) (index) (status)
      (finished : before.table_depths.val.length ≤ index ∨ status ≠ .Ok ()) :
      TableLoopEffect ops before index status (compilerSnapshot before status)
  | step {before middle output result} (index : Usize)
      (inside : index.val < before.table_depths.val.length)
      (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (result, middle))
      (rest : TableLoopEffect ops middle (index.val + 1) result output) :
      TableLoopEffect ops before index.val (.Ok ()) output

/-- Loop inversion retains each published target and the actual stopping state. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops before index status = .ok output) :
    TableLoopEffect ops before index.val status output := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop at called
    rw [loop] at called
    simp only [runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body, bind_ok] at called
    split at called
    next inside =>
      have indexBound : index.val < before.table_depths.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false, Result.ok.injEq] at called
        subst output
        exact .done before index.val (.Err error) (Or.inr (by intro impossible; cases impossible))
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok, bind_ok, ite_true, Std.bind_assoc] at called
        obtain ⟨⟨result, middle⟩, branch, tail⟩ := bind_ok_inv _ _ _ called
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by
          simpa only [UScalar.ofNatCore_val_eq] using arithmetic.2.1
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have continued : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
            ops middle nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
            core.result.Result.is_ok] using tail
        exact .step index indexBound branch (by
          simpa only [progress] using ih _ smaller middle nextIndex result continued rfl)
    next outside =>
      simp only [bind_ok, Result.ok.injEq] at called
      subst output
      exact .done before index.val status (Or.inl (by scalar_tac))

/-- Dispatch lowering retains bounded side-table coordinates, selector decoding,
emission, and the actual target-loop call, including each ordinary error exit. -/
def LowerTableEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ startResult, runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.jump_tables) = .ok startResult ∧
    match startResult with
    | .Err error => status = .Err error ∧ after = before
    | .Ok start => ∃ lengthResult,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.table_depths) = .ok lengthResult ∧
      match lengthResult with
      | .Err error => status = .Err error ∧ after = before
      | .Ok length => ∃ operand,
        runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok operand ∧
        match operand with
        | .Err error => status = .Err error ∧ after = before
        | .Ok selector => ∃ emitted middle,
          runtime.compiler.FunctionCompiler.emit ops before (.JumpTable selector start length) = .ok (emitted, middle) ∧
          match emitted with
          | .Err error => status = .Err error ∧ after = middle
          | .Ok _ => ∃ output,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) = .ok output ∧
            status = snapshotStatus output ∧ after = snapshotCompiler output

/-- One inversion exposes dispatch construction and all target-loop evidence. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (status, after)) :
    LowerTableEffect ops before after status := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at called
  obtain ⟨startResult, startCall, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨startResult, startCall, ?_⟩
  cases startResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨lengthResult, lengthCall, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨lengthResult, lengthCall, ?_⟩
    cases lengthResult with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨operand, operandCall, rest⟩ := bind_ok_inv _ _ _ rest
      refine ⟨operand, operandCall, ?_⟩
      cases operand with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        exact ⟨rest.1.symm, rest.2.symm⟩
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨emitted, middle⟩, emitCall, rest⟩ := bind_ok_inv _ _ _ rest
        refine ⟨emitted, middle, emitCall, ?_⟩
        cases emitted with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          exact ⟨rest.1.symm, rest.2.symm⟩
        | Ok value =>
          cases value
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨output, loopCall, rest⟩ := bind_ok_inv _ _ _ rest
          refine ⟨output, loopCall, ?_⟩
          rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames,
            reachable, nextSource, operands, height, offsets, depths, result⟩
          simp only [uncurry_apply_pair, bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          exact ⟨rest.1.symm, rest.2.symm⟩

/-- Dispatch normality composes emission with a certified target-loop continuation. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (loopReady : ∀ start length selector middle,
      EmittedExact before middle (.JumpTable selector start length) →
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) ⦃ _ => True ⦄) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops before ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step as ⟨startResult, _⟩
  cases startResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨lengthResult, _⟩
    cases lengthResult with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops before 1#usize as ⟨operand, _⟩
      cases operand with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨⟨status, middle⟩, emitted, _⟩ := WP.spec_imp_exists
          (runtime.compiler.FunctionCompiler.emit.total ops law before (.JumpTable selector start length)
            codeFits sourceFits coordinate)
        rw [emitted, bind_ok]
        simp only [uncurry_apply_pair]
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
        | Ok value =>
          cases value
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          have effect := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).2 law).2 rfl
          step with loopReady start length selector middle effect

/-- Independent room for dispatch publication and bounded table coordinates. -/
structure LowerTableDemand {A : Type} (before : runtime.compiler.FunctionCompiler A) (bound : Nat)
    : Prop extends CopyDemand before bound where
  tableStart : before.function.jump_tables.length ≤ U32.max
  depthCount : before.table_depths.length ≤ U32.max

/-- Available dispatch construction delegates the remaining target publication
to a success certificate at the exact emitted intermediate state. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (selector : U32)
    (selectorReady : runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector))
    (demand : LowerTableDemand before bound)
    (post : runtime.compiler.FunctionCompiler A → Prop)
    (loopReady : ∀ start length middle,
      EmittedExact before middle (.JumpTable selector start length) →
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ())
        ⦃ output => snapshotStatus output = .Ok () ∧ post (snapshotCompiler output) ⦄) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops before
      ⦃ (status, after) => status = .Ok () ∧ post after ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step with bounded_index_available (alloc.vec.Vec.len before.function.jump_tables) demand.tableStart
    as ⟨answer, start, accepted, _⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with bounded_index_available (alloc.vec.Vec.len before.table_depths) demand.depthCount
    as ⟨answer, length, accepted, _⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, selectorReady]
  step with runtime.compiler.FunctionCompiler.emit.available ops bound available before (.JumpTable selector start length)
    demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
    demand.coordinate demand.instruction as ⟨answer, middle, accepted, emitted⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with loopReady start length middle emitted as
    ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
      nextSource, operands, height, offsets, depths, result, accepted, effect⟩
  exact ⟨accepted, effect⟩

/-- A single target-loop induction composes a caller's preserved invariant and
terminal postcondition. The index strictly advances regardless of branch status. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.spec {A : Type}
    (ops : runtime.platform.Alloc A)
    (invariant : runtime.compiler.FunctionCompiler A → Nat → core.result.Result Unit Itasca.error.VisitError → Prop)
    (post : CompilerSnapshot A → Prop)
    (advance : ∀ current (index : Usize), invariant current index.val (.Ok ()) →
      index.val < current.table_depths.val.length →
      runtime.compiler.control.FunctionCompiler.table_branch ops current index
        ⦃ (status, after) => invariant after (index.val + 1) status ⦄)
    (finish : ∀ current index status, invariant current index status →
      (current.table_depths.val.length ≤ index ∨ status ≠ .Ok ()) →
      post (compilerSnapshot current status))
    (before : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (held : invariant before index.val status) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops before index status ⦃ post ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
  apply loop.spec_decr_nat (fun p => Usize.max - p.2.1.val)
    (fun p => invariant p.1 p.2.1.val p.2.2)
  · rintro ⟨current, i, result⟩ currentHeld
    dsimp only at currentHeld
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body
    simp only
    split
    next more =>
      have inside : i.val < current.table_depths.val.length := by scalar_tac
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false, WP.spec_ok]
        exact finish current i.val (.Err error) currentHeld (Or.inr (by intro impossible; cases impossible))
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with advance current i currentHeld inside as ⟨result, next, nextHeld⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, by scalar_tac⟩
        have progress : nextIndex.val = i.val + 1 := by scalar_tac
        simpa only [progress] using nextHeld
    next done =>
      simp only [WP.spec_ok]
      exact finish current i.val result currentHeld (Or.inl (by scalar_tac))
  · exact held

/-- Table lowering changes only allocation accounting, branch publication, and
its side-table vector; all reader and source coordinates remain fixed. -/
def TableFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    frames := after.frames
    function := {before.function with
      code := after.function.code
      source_offsets := after.function.source_offsets
      jump_tables := after.function.jump_tables}}

theorem TableFrame.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) : TableFrame before before := rfl

theorem TableFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : TableFrame before middle) (second : TableFrame middle after) : TableFrame before after := by
  unfold TableFrame at *
  rw [second, first]

theorem TableBranchEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index status}
    (effect : TableBranchEffect ops before after index status) : TableFrame before after := by
  obtain ⟨answer, current, called, rest⟩ := effect
  have pc := compiler_pc ops before
  rw [called, WP.spec_ok] at pc
  obtain ⟨budget, same⟩ := pc.2.2
  change current = {before with budget} at same
  subst current
  cases answer with
  | Err error =>
    obtain ⟨_, same⟩ := rest
    subst after
    rfl
  | Ok target =>
    obtain ⟨answer, budget, table, _, rest⟩ := rest
    cases answer with
    | Err error =>
      obtain ⟨_, same⟩ := rest
      subst after
      rfl
    | Ok value =>
      cases value
      obtain ⟨depth, _, called⟩ := rest
      have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ after depth 1#u32 false status called).frame
      unfold TableFrame
      rw [frame]

theorem TableLoopEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before index status output} (effect : TableLoopEffect (A := A) ops before index status output) :
    TableFrame before (snapshotCompiler output) := by
  induction effect with
  | done before index status finished => exact TableFrame.refl before
  | step index inside called rest ih =>
    exact (runtime.compiler.control.FunctionCompiler.table_branch.inv ops _ _ index _ called).frame.trans ih

/-- Successful target publication retains the actual branch call and exact
side-table append, sufficient for all existing target-layout certificates. -/
theorem TableBranchEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize}
    (effect : TableBranchEffect ops before after index (.Ok ()))
    (law : Platform.AllocCorrect ops) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth) :
    ∃ target budget table,
      target.val = before.function.code.val.length ∧
      table.val = before.function.jump_tables.val ++ [target] ∧
      runtime.compiler.control.FunctionCompiler.branch ops
        {before with budget, function := {before.function with jump_tables := table}}
        depth 1#u32 false = .ok (.Ok (), after) := by
  obtain ⟨answer, current, called, rest⟩ := effect
  have pc := compiler_pc ops before
  rw [called, WP.spec_ok] at pc
  obtain ⟨_, coordinate, budget, same⟩ := pc
  change current = {before with budget} at same
  subst current
  cases answer with
  | Err error => cases rest.1
  | Ok target =>
    have targetEq := coordinate target rfl
    obtain ⟨answer, finalBudget, table, pushed, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨found, read, called⟩ := rest
      have inside := (List.getElem?_eq_some_iff.mp lookup).1
      have readSpec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
          before.table_depths index ⦃ out => out = depth ⦄ := by
        step as ⟨out, exactValue⟩
        exact exactValue.trans (List.getElem?_eq_some_iff.mp lookup).2
      rw [read, WP.spec_ok] at readSpec
      subst found
      have tableEq := (budget_push_success ops law budget finalBudget before.function.jump_tables table target pushed).2
      exact ⟨target, finalBudget, table, targetEq, tableEq, called⟩

theorem EmitFrame.table {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EmitFrame before after) : TableFrame before after := by
  unfold TableFrame
  rw [effect]

theorem LowerTableEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : LowerTableEffect ops before after status) : TableFrame before after := by
  obtain ⟨start, _, rest⟩ := effect
  cases start with
  | Err error => exact rest.2 ▸ TableFrame.refl before
  | Ok start =>
    obtain ⟨length, _, rest⟩ := rest
    cases length with
    | Err error => exact rest.2 ▸ TableFrame.refl before
    | Ok length =>
      obtain ⟨operand, _, rest⟩ := rest
      cases operand with
      | Err error => exact rest.2 ▸ TableFrame.refl before
      | Ok selector =>
        obtain ⟨answer, middle, emitted, rest⟩ := rest
        have first := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ answer emitted).1.table
        cases answer with
        | Err error => exact rest.2 ▸ first
        | Ok value =>
          cases value
          obtain ⟨output, called, _, same⟩ := rest
          rw [same]
          exact first.trans (runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv ops middle 0#usize (.Ok ()) output called).frame

/-- Successful dispatch exposes exact coordinates, selector, emission and loop. -/
theorem LowerTableEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : LowerTableEffect ops before after (.Ok ())) (law : Platform.AllocCorrect ops) :
    ∃ start length selector middle output,
      start.val = before.function.jump_tables.val.length ∧
      length.val = before.table_depths.val.length ∧
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector) ∧
      EmittedExact before middle (.JumpTable selector start length) ∧
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) = .ok output ∧
      snapshotStatus output = .Ok () ∧ snapshotCompiler output = after := by
  obtain ⟨start, startCall, rest⟩ := effect
  cases start with
  | Err error => cases rest.1
  | Ok start =>
    have startSpec := bounded_index (alloc.vec.Vec.len before.function.jump_tables)
    rw [startCall, WP.spec_ok] at startSpec
    have startEq := startSpec start rfl
    obtain ⟨length, lengthCall, rest⟩ := rest
    cases length with
    | Err error => cases rest.1
    | Ok length =>
      have lengthSpec := bounded_index (alloc.vec.Vec.len before.table_depths)
      rw [lengthCall, WP.spec_ok] at lengthSpec
      have lengthEq := lengthSpec length rfl
      obtain ⟨operand, operandCall, rest⟩ := rest
      cases operand with
      | Err error => cases rest.1
      | Ok selector =>
        obtain ⟨answer, middle, emitted, rest⟩ := rest
        cases answer with
        | Err error => cases rest.1
        | Ok value =>
          cases value
          obtain ⟨output, called, successful, same⟩ := rest
          exact ⟨start, length, selector, middle, output, startEq, lengthEq, operandCall,
            ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).2 law).2 rfl,
            called, successful.symm, same.symm⟩

end Itasca.Runtime.Compiler

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- One successful table target records its current code PC before lowering
that target's branch. The only intermediate changes are allocation accounting
and the exact append to the retained jump table. -/
theorem compiler_table_branch_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target budget table,
      target.val = before.function.code.val.length ∧
      table.val = before.function.jump_tables.val ++ [target] ∧
      runtime.compiler.control.FunctionCompiler.branch ops
        { before with budget, function := { before.function with jump_tables := table } }
        depth 1#u32 false = .ok (.Ok (),after) := by
  exact (runtime.compiler.control.FunctionCompiler.table_branch.inv ops before after index (.Ok ()) accepted).success law depth lookup

end Itasca.Runtime.Compiler
