import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename

/-!
Sections, each formerly its own module: BranchTableLayout, BranchTableLayoutAlgebra, TableDepths.
-/

/-! ## BranchTableLayout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
/-- An emitted table destination has the ordinary branch layout and exact
transfer/jump fragment for its source depth. -/
def BranchTableEntry (locals : List valtype) (labels : List LabelTarget)
    (stack : List valtype) (code : List Bytecode) (depth : labelidx) (entry : U32) (next : Nat) : Prop :=
  ∃ label dst src count fragmentEnd,
    labels[proj_uN_0 depth]? = some label ∧ label.branchLive = true ∧
    BranchLayout locals stack label dst src count ∧
    Segment code entry.val (branchInstructions dst src count label.target) fragmentEnd ∧
    fragmentEnd ≤ next ∧ next ≤ code.length

/-- Pure compiler evidence for a branch table, including its default entry.
Every retained side-table PC is tied to an emitted branch fragment. -/
structure BranchTableLayout (jumpTables : List U32) (locals : List valtype)
    (labels : List LabelTarget) (stack : List valtype) (code : List Bytecode)
    (depths : List labelidx) (fallback : labelidx) (pc next : Nat)
    (selector start len : U32) : Prop where
  selectorSlot : selector.val = slots locals + slots stack
  length : len.val = depths.length+1
  instruction : code[pc]? = some (.JumpTable selector start len)
  arithmetic : start.val + depths.length ≤ U32.max
  entries : ∀ index depth, (depths ++ [fallback])[index]? = some depth →
    ∃ entry, jumpTables[start.val+index]? = some entry ∧
      BranchTableEntry locals labels stack code depth entry next

end Itasca.Runtime.Compiler

end

/-! ## BranchTableLayoutAlgebra -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem BranchTableEntry.extend {locals labels stack code depth entry next}
    (fragment : BranchTableEntry locals labels stack code depth entry next) (suffix : List Bytecode) :
    BranchTableEntry locals labels stack (code ++ suffix) depth entry next := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  exact ⟨label,dst,src,count,last,foundAt,live,layout,segment.extend suffix,remaining,by simp; omega⟩

theorem BranchTableEntry.relabel {locals labels stack code depth entry next other}
    (fragment : BranchTableEntry locals labels stack code depth entry next) (shape : LabelsShape labels other) :
    BranchTableEntry locals other stack code depth entry next := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  obtain ⟨target,found,same⟩ := shape.lookup foundAt
  refine ⟨target,dst,src,count,last,found,same.branchLive.symm.trans live,?_,?_,remaining,scope⟩
  · simpa only [BranchLayout,← same.front,← same.branchTypes] using layout
  · simpa only [← same.target] using segment

theorem BranchTableEntry.weaken_next {locals labels stack code depth entry next final}
    (fragment : BranchTableEntry locals labels stack code depth entry next)
    (order : next ≤ final) (bound : final ≤ code.length) :
    BranchTableEntry locals labels stack code depth entry final := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  exact ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining.trans order,bound⟩

theorem BranchTableLayout.extend {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (suffix : List Bytecode) :
    BranchTableLayout tables locals labels stack (code ++ suffix) depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,fetch_extend table.instruction suffix,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.extend suffix⟩

theorem BranchTableLayout.relabel {tables locals labels stack code depths fallback pc next selector start len other}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (shape : LabelsShape labels other) :
    BranchTableLayout tables locals other stack code depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.relabel shape⟩

theorem BranchTableLayout.weaken_next {tables locals labels stack code depths fallback pc next selector start len final}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (order : next ≤ final) (bound : final ≤ code.length) :
    BranchTableLayout tables locals labels stack code depths fallback pc final selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.weaken_next order bound⟩

theorem BranchTableLayout.append_tables {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (suffix : List U32) :
    BranchTableLayout (tables ++ suffix) locals labels stack code depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]; exact lookup,fragment⟩
end Itasca.Runtime.Compiler

end

/-! ## TableDepths -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_emit_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status accepted).1
  change after = _ at frame
  rw [frame]

theorem compiler_copy_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  have frame := (runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count status accepted).frame
  change after = _ at frame
  rw [frame]

theorem compiler_pc_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  exact congrArg (fun c => c.table_depths) same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl


open Lean Meta Elab Tactic in
elab "depths_effect " h:ident " using " ops:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_depths $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_depths $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc =>
      `(tactic| have effect := compiler_pc_depths $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch =>
      `(tactic| have effect := compiler_patch_depths $ops _ _ _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.branch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_branch_depths
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac

macro "depths_close" : tactic => `(tactic| first | rfl | simp_all only [Prod.mk.injEq])
macro "depths_step " h:ident " using " ops:term : tactic => `(tactic|
  first
  | solve | (depths_effect $h using $ops; depths_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; depths_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try depths_effect called using $ops
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

theorem compiler_branch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' depths_step accepted using ops

theorem compiler_table_branch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' depths_step accepted using ops
end Itasca.Runtime.Compiler

end
