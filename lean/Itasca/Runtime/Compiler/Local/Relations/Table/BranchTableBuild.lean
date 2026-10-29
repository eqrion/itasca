import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ObservationLayout
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableArguments
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSuccess
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths

/-!
Construction of br_table targets with their emitted heights and table correspondence. TableTargetsBuilt records the target-by-target invariant consumed by loop proofs.
-/

/-! ## Branch Table Height -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_emit_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.height = before.height := by
  unfold runtime.compiler.FunctionCompiler.emit at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, _, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨_, output⟩ := rest
          subst after
          rfl
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl

theorem compiler_copy_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.height = before.height := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    rfl
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      rfl
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_branch_height ops before after instruction status emitted

theorem compiler_pc_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.height = before.height := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  exact congrArg (fun c => c.height) same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.height = before.height := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl



open Lean Meta Elab Tactic in
elab "branch_height_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_branch_height $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_branch_height $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_branch_height
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_branch_height
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "branch_height_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq]; try omega)))
macro "branch_height_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; branch_height_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (branch_height_effect $h using $ops, $law; branch_height_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; branch_height_close)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try branch_height_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)




theorem compiler_branch_height_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.height = before.height := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' branch_height_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Target -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact syntactic effect of a table arm. Forward destinations retain their
new relocation site; loop arms retain the already resolved backedge. -/
inductive TableTargetCode {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (depth : U32) : Prop where
  | loop (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind = .Loop)
      (operands : source.val + frame.params.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.params frame.start_pc)
      (frames : after.frames = before.frames) : TableTargetCode before after depth
  | forward (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (fixups : alloc.vec.Vec Usize) (site : Usize)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind ≠ .Loop)
      (operands : source.val + frame.results.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.results core.num.U32.MAX)
      (frames : after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups})
      (appended : fixups.val = frame.fixups.val ++ [site])
      (sitePosition : site.val = before.function.code.val.length +
        (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1)) :
      TableTargetCode before after depth

/-- Successful actual arm lowering establishes the complete exact code/fixup
certificate, including source operand safety from its accepted checked arithmetic. -/
theorem compiler_table_target_code {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target,
      target.val = before.function.code.val.length ∧
      after.function.jump_tables.val = before.function.jump_tables.val ++ [target] ∧
      after.height = before.height ∧
      TableTargetCode before after depth := by
  obtain ⟨target,budget,table,targetEq,tableEq,branchCall⟩ :=
    compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branchCall
  have tables := compiler_branch_tables ops law staged after depth 1#u32 false branchCall
  have tableAfter := congrArg CompilerTables.jumpTables tables
  change after.function.jump_tables.val = table.val at tableAfter
  have height := compiler_branch_height_result ops law staged after depth 1#u32 false (.Ok ()) branchCall
  obtain ⟨frameIndex,frame,source,found,position,operands⟩ :=
    compiler_branch_arguments_success ops staged after depth 1#u32 branchCall
  refine ⟨target,targetEq,tableAfter.trans tableEq,height,?_⟩
  by_cases isLoop : frame.kind = .Loop
  · have width : source.val + frame.params.val + (1#u32).val = staged.height.val := by
      simpa only [frameBranchWidth,isLoop] using operands
    obtain ⟨code,frames⟩ := compiler_branch_loop_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .loop frameIndex frame source found position isLoop width code frames
  · have width : source.val + frame.results.val + (1#u32).val = staged.height.val := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    obtain ⟨fixups,frames,_,code,site,sitePosition,appended⟩ := compiler_branch_forward_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .forward frameIndex frame source fixups site found position isLoop width code frames appended sitePosition
end Itasca.Runtime.Compiler

end

/-! ## Branch Table Build -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Syntax-only production certificate for the ordered branch fragments. Each
entry records its actual dispatch PC and exact relocation or loop backedge. -/
inductive TableTargetsBuilt {A : Type} : runtime.compiler.FunctionCompiler A →
    runtime.compiler.FunctionCompiler A → List U32 → List U32 → Prop where
  | nil (compiler) : TableTargetsBuilt compiler compiler [] []
  | cons {before middle after depths targets} (depth target : U32)
      (targetPC : target.val = before.function.code.val.length)
      (appended : middle.function.jump_tables.val = before.function.jump_tables.val ++ [target])
      (height : middle.height = before.height)
      (depthsSame : middle.table_depths = before.table_depths)
      (fragment : TableTargetCode before middle depth)
      (rest : TableTargetsBuilt middle after depths targets) :
      TableTargetsBuilt before after (depth :: depths) (target :: targets)

theorem TableTargetsBuilt.tables {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    after.function.jump_tables.val = before.function.jump_tables.val ++ targets := by
  induction built with
  | nil => simp
  | cons depth target pc appended height same fragment rest ih =>
    rw [ih,appended]
    simp

theorem TableTargetsBuilt.length {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    targets.length = depths.length := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => simpa using ih

theorem TableTargetsBuilt.height {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    after.height = before.height := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ height _ _ _ ih => exact ih.trans height

/-- Eliminate every actual call in the accepted finite loop into its exact
ordered code/table effect. The result has no execution-correctness premise. -/
theorem TableBranchRun.built {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    ∃ targets, TableTargetsBuilt before after (before.table_depths.val.drop index) targets := by
  induction run with
  | done compiler index finished =>
    exact ⟨[], by simpa only [List.drop_eq_nil_of_le finished] using TableTargetsBuilt.nil compiler⟩
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := by simp [depth,inside]
    obtain ⟨target,pc,appended,height,fragment⟩ :=
      compiler_table_target_code ops law before middle index depth lookup called
    have same := compiler_table_branch_depths ops before middle index (.Ok ()) called
    obtain ⟨targets,built⟩ := ih
    rw [same] at built
    refine ⟨target::targets, ?_⟩
    have split : before.table_depths.val.drop index.val =
        depth :: before.table_depths.val.drop (index.val+1) := by
      exact List.drop_eq_getElem_cons inside
    rw [split]
    exact .cons depth target pc appended height same fragment built
theorem TableTargetCode.code_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) :
    ∃ fragment, after.function.code.val = before.function.code.val ++ fragment ∧ 1 ≤ fragment.length := by
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    exact ⟨_,code,by simp only [branchInstructions]; split <;> simp⟩
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    exact ⟨_,code,by simp only [branchInstructions]; split <;> simp⟩

theorem TableTargetsBuilt.code_prefix {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    ∃ fragment, after.function.code.val = before.function.code.val ++ fragment ∧ depths.length ≤ fragment.length := by
  induction built with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons depth target pc appended height same effect rest ih =>
    obtain ⟨first,firstCode,firstLength⟩ := effect.code_prefix
    obtain ⟨remaining,restCode,restLength⟩ := ih
    exact ⟨first++remaining,by rw [restCode,firstCode,List.append_assoc],by simp only [List.length_append,List.length_cons]; omega⟩
end Itasca.Runtime.Compiler

end
