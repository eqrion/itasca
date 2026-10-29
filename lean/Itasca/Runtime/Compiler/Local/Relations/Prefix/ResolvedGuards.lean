import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FrameSites

/-!
Resolution schedules can be divided at a selected IF guard.

Main declarations: `resolved_code_append_groups` and `FramePlans.away_guard`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Resolution schedules can be divided at a selected IF guard. -/
theorem resolved_code_append_groups (code : List Bytecode) (left right : List FixupTarget) :
    resolvedCode code (left ++ right) = resolvedCode (resolvedCode code left) right := by
  induction left generalizing code with
  | nil => rfl
  | cons group rest ih => exact ih _

/-- Groups which do not name an instruction leave its exact operands intact. -/
theorem resolved_code_away (code : List Bytecode) (groups : List FixupTarget) (index : Nat)
    (away : ∀ group ∈ groups, ∀ site ∈ group.sites, site.val ≠ index) :
    (resolvedCode code groups)[index]? = code[index]? := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih =>
    rw [resolvedCode, ih _ (fun g member => away g (List.mem_cons_of_mem _ member)), patch_code_get]
    have absent : ¬ ∃ site ∈ group.sites, site.val = index := by
      rintro ⟨site, member, equal⟩
      exact away group (by simp) site member equal
    simp [absent]

theorem resolved_code_guard (code : List Bytecode) (before after : List FixupTarget)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (away : ∀ group ∈ before ++ after, ∀ site ∈ group.sites, site.val ≠ guard.val) :
    (resolvedCode code (before ++ ⟨[guard], target⟩ :: after))[guard.val]? =
      some (.JumpIfZero condition target) := by
  rw [resolved_code_append_groups, resolvedCode]
  rw [resolved_code_away _ _ _ (fun group member => away group (List.mem_append_right _ member))]
  rw [patch_code_get, resolved_code_away _ _ _ (fun group member => away group (List.mem_append_left _ member))]
  simp [found, retarget]

/-- A schedule contains only frame guards and forward-branch sites. Thus a
physical IF guard belonging to none of these frames is untouched by it. -/
theorem FramePlans.away_guard {length locals frames labels groups code}
    (plans : FramePlans length locals frames labels groups)
    (sitesOk : ∀ frame ∈ frames, FrameSites code frame)
    {guard : Usize} {condition old}
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (distinct : ∀ frame ∈ frames, frame.if_pc ≠ some guard) :
    ∀ group ∈ groups, ∀ site ∈ group.sites, site.val ≠ guard.val := by
  induction plans with
  | nil => simp
  | @push frames labels groups prior frame label guardTarget future ih =>
    have current := sitesOk frame (by simp)
    have rest := ih (fun f member => sitesOk f (List.mem_append_left _ member))
      (fun f member => distinct f (List.mem_append_left _ member))
    intro group member site atSite
    rcases List.mem_append.mp member with first | remaining
    · simp only [frameGroups, List.mem_append, List.mem_singleton] at first
      rcases first with guarded | rfl
      · cases guardEq : frame.if_pc with
        | none => simp [guardEq] at guarded
        | some other =>
          simp only [guardEq, List.mem_singleton] at guarded
          subst group
          simp only [List.mem_singleton] at atSite
          subst site
          intro same
          have scalarSame : other = guard := by scalar_tac
          exact distinct frame (by simp) (guardEq.trans (congrArg some scalarSame))
      · exact current.branches.not_guard found site atSite
    · exact rest group remaining site atSite

end Itasca.Runtime.Compiler
