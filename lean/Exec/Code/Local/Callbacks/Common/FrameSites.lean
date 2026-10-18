import Exec.Code.Local.Relations.Common.FutureFrames
namespace Exec.Code
open Aeneas.Std

/-- Forward label fixups never name an IF guard. The two branch constructors
are recorded directly from the compiler's emission, without an execution claim. -/
def ForwardSites (code : List Bytecode) (sites : List Usize) : Prop :=
  ∀ site, site ∈ sites → (∃ target, code[site.val]? = some (.Jump target)) ∨
    (∃ condition target, code[site.val]? = some (.JumpIfNonZero condition target))

structure FrameSites (code : List Bytecode) (frame : runtime.compiler.Frame) : Prop where
  branches : ForwardSites code frame.fixups.val
  guard : ∀ site, frame.if_pc = some site →
    ∃ condition target, code[site.val]? = some (.JumpIfZero condition target)

theorem ForwardSites.inside {code sites} (sitesOk : ForwardSites code sites) :
    ∀ site, site ∈ sites → site.val < code.length := by
  intro site member
  rcases sitesOk site member with ⟨target, found⟩ | ⟨condition, target, found⟩
  all_goals exact (List.getElem?_eq_some_iff.mp found).1

theorem ForwardSites.branches {code sites} (sitesOk : ForwardSites code sites) :
    BranchSites code sites := by
  intro site member
  rcases sitesOk site member with ⟨target, found⟩ | ⟨condition, target, found⟩
  · exact ⟨.jump, target, found⟩
  · exact ⟨.nonzero condition, target, found⟩

theorem ForwardSites.not_guard {code sites} (sitesOk : ForwardSites code sites)
    {guard condition target} (found : code[guard]? = some (.JumpIfZero condition target)) :
    ∀ site, site ∈ sites → site.val ≠ guard := by
  intro site member equal
  rcases sitesOk site member with ⟨target, branch⟩ | ⟨condition, target, branch⟩
  all_goals rw [equal, found] at branch; cases branch

theorem FrameSites.inside {code frame} (sitesOk : FrameSites code frame)
    (label : LabelTarget) (guardTarget : U32) :
    FixupsInside (frameGroups frame label guardTarget) code.length := by
  intro group member site atSite
  simp only [frameGroups, List.mem_append, List.mem_singleton] at member
  rcases member with guardGroup | rfl
  · cases guardEq : frame.if_pc with
    | none => simp [guardEq] at guardGroup
    | some guard =>
      simp only [guardEq, List.mem_singleton] at guardGroup
      subst group
      simp only [List.mem_singleton] at atSite
      subst site
      obtain ⟨condition, target, found⟩ := sitesOk.guard guard guardEq
      exact (List.getElem?_eq_some_iff.mp found).1
  · exact sitesOk.branches.inside site atSite

theorem FramePlans.inside {length locals frames labels groups code}
    (plans : FramePlans length locals frames labels groups)
    (sitesOk : ∀ frame ∈ frames, FrameSites code frame) : FixupsInside groups code.length := by
  induction plans with
  | nil => simp [FixupsInside]
  | @push frames labels groups prior frame label guardTarget future ih =>
    have top := (sitesOk frame (by simp)).inside label guardTarget
    have rest := ih (fun f member => sitesOk f (List.mem_append_left _ member))
    intro group member site atSite
    rcases List.mem_append.mp member with first | remaining
    · exact top group first site atSite
    · exact rest group remaining site atSite

theorem ForwardSites.extend {code sites} (sitesOk : ForwardSites code sites) (suffix : List Bytecode) :
    ForwardSites (code ++ suffix) sites := by
  intro site member
  have bound := sitesOk.inside site member
  simpa only [List.getElem?_append_left bound] using sitesOk site member

theorem FrameSites.extend {code frame} (sitesOk : FrameSites code frame) (suffix : List Bytecode) :
    FrameSites (code ++ suffix) frame := by
  refine ⟨sitesOk.branches.extend suffix, ?_⟩
  intro site atSite
  obtain ⟨condition, target, found⟩ := sitesOk.guard site atSite
  exact ⟨condition, target, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩

theorem ForwardSites.patch {code sites} (sitesOk : ForwardSites code sites)
    (changed : List Usize) (target : U32) : ForwardSites (patchCode code changed target) sites := by
  intro site member
  rw [patchCode_get]
  rcases sitesOk site member with ⟨old, found⟩ | ⟨condition, old, found⟩
  · split
    · exact Or.inl ⟨target, by simp [found, retarget]⟩
    · exact Or.inl ⟨old, found⟩
  · split
    · exact Or.inr ⟨condition, target, by simp [found, retarget]⟩
    · exact Or.inr ⟨condition, old, found⟩

theorem FrameSites.patch {code frame} (sitesOk : FrameSites code frame)
    (changed : List Usize) (target : U32) : FrameSites (patchCode code changed target) frame := by
  refine ⟨sitesOk.branches.patch changed target, ?_⟩
  intro site atSite
  obtain ⟨condition, old, found⟩ := sitesOk.guard site atSite
  rw [patchCode_get]
  split
  · exact ⟨condition, target, by simp [found, retarget]⟩
  · exact ⟨condition, old, found⟩

end Exec.Code
