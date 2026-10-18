import Exec.Code.Local.Callbacks.Common.FrameSites
namespace Exec.Code
open Aeneas.Std

/-- Resolution schedules can be divided at a selected IF guard. -/
theorem resolvedCode_append_groups (code : List Bytecode) (left right : List FixupTarget) :
    resolvedCode code (left ++ right) = resolvedCode (resolvedCode code left) right := by
  induction left generalizing code with
  | nil => rfl
  | cons group rest ih => exact ih _

/-- Groups which do not name an instruction leave its exact operands intact. -/
theorem resolvedCode_away (code : List Bytecode) (groups : List FixupTarget) (index : Nat)
    (away : ∀ group ∈ groups, ∀ site ∈ group.sites, site.val ≠ index) :
    (resolvedCode code groups)[index]? = code[index]? := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih =>
    rw [resolvedCode, ih _ (fun g member => away g (List.mem_cons_of_mem _ member)), patchCode_get]
    have absent : ¬ ∃ site ∈ group.sites, site.val = index := by
      rintro ⟨site, member, equal⟩
      exact away group (by simp) site member equal
    simp [absent]

theorem resolvedCode_guard (code : List Bytecode) (before after : List FixupTarget)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (away : ∀ group ∈ before ++ after, ∀ site ∈ group.sites, site.val ≠ guard.val) :
    (resolvedCode code (before ++ ⟨[guard], target⟩ :: after))[guard.val]? =
      some (.JumpIfZero condition target) := by
  rw [resolvedCode_append_groups, resolvedCode]
  rw [resolvedCode_away _ _ _ (fun group member => away group (List.mem_append_right _ member))]
  rw [patchCode_get, resolvedCode_away _ _ _ (fun group member => away group (List.mem_append_left _ member))]
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

/-- The innermost IF guard resolves to its planned ELSE/END coordinate.
Forward branch fixups cannot overwrite it, even when some lists have duplicate
branch sites. Only distinctness from the other active guards is needed. -/
theorem FramePlans.top_guard {length locals frames labels groups code}
    (plans : FramePlans length locals frames labels groups)
    (sitesOk : ∀ frame ∈ frames, FrameSites code frame)
    (frame : runtime.compiler.Frame) (current : FrameSites code frame)
    (label : LabelTarget) (target : U32) (guard : Usize)
    (guardEq : frame.if_pc = some guard)
    (distinct : ∀ other ∈ frames, other.if_pc ≠ some guard) :
    ∃ condition, (resolvedCode code (frameGroups frame label target ++ groups))[guard.val]? =
      some (.JumpIfZero condition target) := by
  obtain ⟨condition, old, found⟩ := current.guard guard guardEq
  refine ⟨condition, ?_⟩
  have rest := plans.away_guard sitesOk found distinct
  have branch := current.branches.not_guard found
  have resolved := resolvedCode_guard code [] (⟨frame.fixups.val, label.target⟩ :: groups)
    guard condition old target found (by
      intro group member site atSite
      simp only [List.nil_append, List.mem_cons] at member
      rcases member with rfl | member
      · exact branch site atSite
      · exact rest group member site atSite)
  simpa [frameGroups, guardEq] using resolved

end Exec.Code
