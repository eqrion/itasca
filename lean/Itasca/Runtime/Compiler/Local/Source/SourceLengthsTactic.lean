import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Pair
import Itasca.Runtime.Compiler.Local.Relations.Emission.EmissionSources
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.PatchGrowth
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename

/-!
Sections, each formerly its own module: SourceLengths, SourceLengthsTactic.
-/

/-! ## SourceLengths -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Code and source coordinates grow by the same number of entries. -/
def SourceProgress {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after.function.code.val.length + before.function.source_offsets.val.length =
    before.function.code.val.length + after.function.source_offsets.val.length

/-- Every retained instruction has a source coordinate. -/
def SourceAligned {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  compiler.function.source_offsets.val.length = compiler.function.code.val.length

theorem SourceProgress.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    SourceProgress compiler compiler := rfl

theorem SourceProgress.trans {A : Type} {first middle last : runtime.compiler.FunctionCompiler A}
    (left : SourceProgress first middle) (right : SourceProgress middle last) :
    SourceProgress first last := by unfold SourceProgress at *; omega

theorem SourceProgress.aligned {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (progress : SourceProgress before after) (aligned : SourceAligned before) :
    SourceAligned after := by unfold SourceProgress SourceAligned at *; omega

theorem compiler_emit_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    SourceProgress before after := by
  have code := compiler_emit_code_success ops law before after instruction accepted
  have sources := compiler_emit_source_length_success ops law before after instruction accepted
  simp [SourceProgress, code, sources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem compiler_observe_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    SourceProgress before after := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  rw [frame]
  rfl

theorem compiler_copy_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    SourceProgress before after := by
  rcases runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count (.Ok ()) accepted with
    ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · subst after
    exact rfl
  · exact compiler_emit_sources ops law before after _ emitted

theorem compiler_finish_op_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (), after)) :
    SourceProgress before after := by
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) accepted).success
  exact (compiler_emit_sources ops law before middle instruction emitted).trans
    (compiler_observe_sources ops law middle after state (.Ok ()) rest)

theorem compiler_pair_sources {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    SourceProgress before after := by
  have frame := (runtime.compiler.FunctionCompiler.pair.inv ops before after a b status accepted).1
  change after = _ at frame
  rw [frame]
  rfl

/-- PC calculation may reject its range but only updates the budget. -/
theorem compiler_pc_sources {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    SourceProgress before after := by
  have result := compiler_pc ops before
  rw [accepted, WP.spec_ok] at result
  obtain ⟨_, _, budget, same⟩ := result
  change after = {before with budget} at same
  subst after
  rfl

theorem compiler_emit_sources_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    status = .Ok () → SourceProgress before after := by
  intro success
  subst status
  exact compiler_emit_sources ops law before after instruction accepted

theorem compiler_copy_sources_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    status = .Ok () → SourceProgress before after := by
  intro success
  subst status
  exact compiler_copy_sources ops law before after dst src count accepted

theorem compiler_finish_op_sources_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    status = .Ok () → SourceProgress before after := by
  intro success
  subst status
  exact compiler_finish_op_sources ops law before after state instruction accepted
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_sources_unchanged {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.function.source_offsets = before.function.source_offsets := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl


theorem compiler_patch_sources {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    SourceProgress before after := by
  have code := compiler_patch_code_length ops before after pc target status accepted
  have sources := compiler_patch_sources_unchanged ops before after pc target status accepted
  simp [SourceProgress, code, sources]
theorem compiler_fixups_sources_unchanged {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.source_offsets = before.function.source_offsets := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
      bind_ok] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
            ops middle sites target nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
            core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex result tail' rfl).trans
          (compiler_patch_sources_unchanged ops before middle site target result patched)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem compiler_fixups_after_if_sources_unchanged {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.source_offsets = before.function.source_offsets :=
  compiler_fixups_sources_unchanged ops before sites target index status output accepted

theorem compiler_fixups_sources {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    SourceProgress before (snapshotCompiler output) := by
  have code := compiler_fixups_code_length ops before sites target index status output accepted
  have sources := compiler_fixups_sources_unchanged ops before sites target index status output accepted
  simp [SourceProgress, code, sources]

theorem compiler_fixups_after_if_sources {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    SourceProgress before (snapshotCompiler output) := by
  have code := compiler_fixups_after_if_code_length ops before sites target index status output accepted
  have sources := compiler_fixups_after_if_sources_unchanged ops before sites target index status output accepted
  simp [SourceProgress, code, sources]

end Itasca.Runtime.Compiler

end

/-! ## SourceLengthsTactic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
open Lean Meta Elab Tactic in
elab "sources_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_sources $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_sources_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_sources_result $ops $law _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_sources $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_sources_result $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_sources
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac

theorem source_unit_eq (value : Unit) : value = () := Subsingleton.elim _ _

macro "sources_close" : tactic => `(tactic|
  (first | rfl | (simp_all [SourceProgress, snapshotCompiler, source_unit_eq]; try omega)))

open Lean Meta Elab Tactic in
elab "sources_nonterminal " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  unless lhs.isAppOf ``Aeneas.Std.bind do throwError "not a bind equation"

open Lean Meta Elab Tactic in
elab "sources_terminal " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  unless lhs.isAppOf ``Result.ok do throwError "nonterminal equation"

open Lean Meta Elab Tactic in
elab "sources_split " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some matcherName := lhs.getAppFn.constName? | throwError "not a matcher"
  unless matcherName == ``ite || matcherName == ``dite || (← isMatcher matcherName) do
    throwError "not a matcher"
  evalTactic (← `(tactic| split at $h:ident))

macro "sources_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; sources_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (sources_effect $h using $ops, $law; sources_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; sources_close)
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
     try sources_effect called using $ops, $law
     try clear called
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

end Itasca.Runtime.Compiler

end
