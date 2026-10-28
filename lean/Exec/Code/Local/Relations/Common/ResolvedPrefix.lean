import Exec.Code.Local.Callbacks.Common.FixupAlgebra
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- One open label's retained physical fixup sites and its eventual static exit.
The target is a source-layout coordinate, not an execution predicate. -/
structure FixupTarget where
  sites : List Usize
  target : U32

def resolvedCode (code : List Bytecode) : List FixupTarget → List Bytecode
  | [] => code
  | group :: rest => resolvedCode (patchCode code group.sites group.target) rest

def FixupsInside (groups : List FixupTarget) (length : Nat) : Prop :=
  ∀ group, group ∈ groups → ∀ site, site ∈ group.sites → site.val < length

theorem resolvedCode_length (code : List Bytecode) (groups : List FixupTarget) :
    (resolvedCode code groups).length = code.length := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih => simp [resolvedCode, ih, patchCode_length]

theorem resolvedCode_append_code (code emitted : List Bytecode) (groups : List FixupTarget)
    (inside : FixupsInside groups code.length) :
    resolvedCode (code ++ emitted) groups = resolvedCode code groups ++ emitted := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih =>
    simp only [resolvedCode]
    rw [patchCode_append_code _ _ _ _ (inside group (by simp))]
    apply ih
    intro g member site atSite
    simpa [patchCode_length] using inside g (List.mem_cons_of_mem _ member) site atSite

/-- A newly emitted forward branch belongs to exactly its selected label group.
Resolving that extended schedule appends the branch with its final static target
and leaves all earlier resolved instructions unchanged. -/
theorem resolvedCode_new_branch (code emitted : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (kind : BranchKind) (old : U32) (site : Usize)
    (position : site.val = code.length + emitted.length)
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ emitted ++ [kind.instruction old])
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ emitted ++ [kind.instruction group.target] := by
  induction before generalizing code with
  | nil =>
    simp only [List.nil_append, resolvedCode]
    rw [patchCode_new_branch code emitted group.sites kind old group.target site position
      (inside group (by simp))]
    rw [List.append_assoc, resolvedCode_append_code]
    · simp [List.append_assoc]
    · intro g member pc atPc
      simpa [patchCode_length] using inside g (by simp [member]) pc atPc
  | cons head rest ih =>
    simp only [List.cons_append, resolvedCode]
    have headInside : ∀ pc, pc ∈ head.sites → pc.val < code.length :=
      inside head (by simp)
    rw [List.append_assoc, patchCode_append_code _ _ _ _ headInside, ← List.append_assoc]
    apply ih
    · simpa [patchCode_length] using position
    · intro g member pc atPc
      simpa [patchCode_length] using inside g (List.mem_cons_of_mem _ member) pc atPc

end Itasca.Runtime.Code
