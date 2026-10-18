import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Callbacks.Common.Fixups
namespace Exec.Code
open Aeneas Aeneas.Std

theorem Segment.single {code : List Bytecode} {pc : Nat} {instruction : Bytecode}
    (found : code[pc]? = some instruction) : Segment code pc [instruction] (pc + 1) := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have element : code[pc] = instruction := (List.getElem?_eq_some_iff.mp found).2
  refine ⟨code.take pc, code.drop (pc + 1), ?_, by simp; omega, by simp⟩
  have take := List.take_concat_get' code pc bound
  rw [← element, take]
  exact (List.take_append_drop (pc + 1) code).symm

/-- Copy instructions are unaffected even when a fixup list is duplicated or
contains their coordinate; retargeting only changes branch constructors. -/
theorem patchCode_fixed (code : List Bytecode) (sites : List Usize) (target : U32)
    (pc : Nat) (instruction : Bytecode)
    (fixed : retarget instruction target = instruction)
    (found : code[pc]? = some instruction) :
    (patchCode code sites target)[pc]? = some instruction := by
  induction sites generalizing code with
  | nil => exact found
  | cons site rest ih =>
    simp only [patchCode]
    split
    · rename_i old lookup
      apply ih
      by_cases same : pc = site.val
      · have eq : old = instruction := by rw [← same, found] at lookup; exact Option.some.inj lookup.symm
        subst old
        have bound := (List.getElem?_eq_some_iff.mp found).1
        simp [← same, fixed, bound]
      · simpa [Ne.symm same] using found
    · exact ih code found

def BranchHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧ code[pc]? = some (.Jump 4294967295#u32)
  else
    code[pc]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 1 ∧ code[pc + 1]? = some (.Jump 4294967295#u32)

/-- Resolving a label's actual fixup list constructs the complete static branch
sequence, preserving a preceding transfer without an execution premise. -/
theorem BranchHole.resolve {code sites pc dst src count} (hole : BranchHole code sites pc dst src count)
    (target : U32) : Segment (patchCode code sites target) pc
      (branchInstructions dst src count target) (pc + (branchInstructions dst src count target).length) := by
  by_cases empty : count = 0#u32 ∨ src = dst
  · simp only [BranchHole, if_pos empty] at hole
    obtain ⟨site, member, position, fetched⟩ := hole
    have patched := patchCode_target code sites target 4294967295#u32 site .jump member (by simpa [position, BranchKind.instruction] using fetched)
    simp only [branchInstructions, if_pos empty, List.length_singleton]
    exact Segment.single (by simpa [position, BranchKind.instruction] using patched)
  · simp only [BranchHole, if_neg empty] at hole
    obtain ⟨copied, site, member, position, fetched⟩ := hole
    have copyFixed : retarget (transferInstruction dst src count) target = transferInstruction dst src count := by
      unfold transferInstruction
      split <;> first | rfl | split <;> rfl
    have copyPreserved := patchCode_fixed code sites target pc _ copyFixed copied
    have patched := patchCode_target code sites target 4294967295#u32 site .jump member (by simpa [position, BranchKind.instruction] using fetched)
    have first := Segment.single copyPreserved
    have second := Segment.single (by simpa [position, BranchKind.instruction] using patched)
    have together := first.append second
    simpa [branchInstructions, empty, Nat.add_assoc] using together

/-- The checked extracted fixup loop discharges a retained source BR hole into
CodeRel; no runtime or compiler-correctness premise is assumed. -/
@[step] theorem compiler_fixups_branch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (types functions : List functype) (returns locals stack final : List valtype)
    (labels : List LabelTarget) (depth pc : Nat) (label : LabelTarget)
    (dst src count : U32) (sourceTail : List instr)
    (lookup : labels[depth]? = some label)
    (live : label.branchLive = true)
    (layout : BranchLayout locals stack label dst src count)
    (branches : BranchSites compiler.function.code.val sites.val)
    (hole : BranchHole compiler.function.code.val sites.val pc dst src count) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops compiler sites label.target 0#usize (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧ OnlyCode compiler after ∧
        CodeRel types functions returns locals after.function.code.val labels stack
          (.BR (.mk_uN depth) :: sourceTail) pc
          (pc + (branchInstructions dst src count label.target).length) final ⦄ := by
  apply WP.spec_mono (compiler_fixups ops compiler sites label.target 0#usize (by simp) branches)
  rintro out ⟨after, output, onlyCode, effect⟩
  refine ⟨after, output, onlyCode, CodeRel.branch lookup live layout ?_ (Nat.le_refl _) ?_⟩
  · simpa [effect] using hole.resolve label.target
  · simpa [effect] using (hole.resolve label.target).next_bound

/-- A pending branch keeps its source stack and layout, rather than just an
untyped numeric patch address. This is the branch component of the open-label
compiler invariant. -/
structure PendingBranch where
  pc : Nat
  depth : Nat
  stack : List valtype
  dst : U32
  src : U32
  count : U32
  sourceTail : List instr

/-- Open label frames retain all source BR holes that will be resolved together. -/
def OpenBranches (locals : List valtype) (code : List Bytecode)
    (labels : List LabelTarget) (target : U32) (sites : List Usize) (pending : List PendingBranch) : Prop :=
  ∀ branch, branch ∈ pending → ∃ label,
    labels[branch.depth]? = some label ∧ label.branchLive = true ∧ label.target = target ∧
    BranchLayout locals branch.stack label branch.dst branch.src branch.count ∧
    BranchHole code sites branch.pc branch.dst branch.src branch.count


@[step] theorem compiler_fixups_open_branches {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (types functions : List functype) (returns locals final : List valtype)
    (labels : List LabelTarget) (target : U32) (pending : List PendingBranch)
    (branches : BranchSites compiler.function.code.val sites.val)
    (invariant : OpenBranches locals compiler.function.code.val labels target sites.val pending) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops compiler sites target 0#usize (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧ OnlyCode compiler after ∧
        ∀ branch, branch ∈ pending →
          CodeRel types functions returns locals after.function.code.val labels branch.stack
            (.BR (.mk_uN branch.depth) :: branch.sourceTail) branch.pc
            (branch.pc + (branchInstructions branch.dst branch.src branch.count target).length) final ⦄ := by
  apply WP.spec_mono (compiler_fixups ops compiler sites target 0#usize (by simp) branches)
  rintro out ⟨after, output, onlyCode, effect⟩
  refine ⟨after, output, onlyCode, ?_⟩
  intro branch member
  obtain ⟨label, lookup, live, sameTarget, layout, hole⟩ := invariant branch member
  have resolved := hole.resolve target
  apply CodeRel.branch lookup live layout (by simpa [effect, sameTarget] using resolved) (Nat.le_refl _)
  simpa [effect] using resolved.next_bound

end Exec.Code
