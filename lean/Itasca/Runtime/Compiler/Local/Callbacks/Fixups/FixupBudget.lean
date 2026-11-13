import Itasca.Runtime.Compiler.Local.Relations.Prefix.FutureFrames

/-!
Sections, each formerly its own module: FrameSites, FramePlanPop, FramePlanUpdate, FixupBudget.
-/

/-! ## FrameSites -/

section

/-!
Forward label fixups never name an IF guard. The two branch constructors are recorded directly from the compiler's emission, without an execution claim.

Main declarations: `ForwardSites` and `FrameSites`. A direct consumer is `Compiler.Local.Callbacks.Control.ElseSafety`.
-/

namespace Itasca.Runtime.Compiler
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
  rw [patch_code_get]
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
  rw [patch_code_get]
  split
  · exact ⟨condition, target, by simp [found, retarget]⟩
  · exact ⟨condition, old, found⟩

end Itasca.Runtime.Compiler

end

/-! ## FramePlanPop -/

section

/-!
Invert the compiler's physical push without losing the source label or that frame's separate guard and branch resolution groups.

Main declarations: `FramePlans.pop`. A direct consumer is `Compiler.Local.Callbacks.Control.ElseFrames`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Invert the compiler's physical push without losing the source label or
that frame's separate guard and branch resolution groups. -/
theorem FramePlans.pop {length locals frames frame labels groups}
    (plans : FramePlans length locals (frames ++ [frame]) labels groups) :
    ∃ label outer pending guardTarget,
      labels = label :: outer ∧ groups = frameGroups frame label guardTarget ++ pending ∧
      FramePlans length locals frames outer pending ∧
      FrameFuture length locals frame label guardTarget := by
  generalize shape : frames ++ [frame] = physical at plans
  cases plans with
  | nil => simp at shape
  | @push old labels groups prior current label guardTarget future =>
    have size : frames.length = old.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append, List.length_singleton] at lengths
      omega
    obtain ⟨sameFrames, sameFrame⟩ := List.append_inj shape size
    simp only [List.cons.injEq, and_true] at sameFrame
    subst old current
    exact ⟨label, labels, groups, guardTarget, rfl, rfl, prior, future⟩

end Itasca.Runtime.Compiler

end

/-! ## FramePlanUpdate -/

section

/-!
A future plan after recording a forward branch yields the corresponding plan before it. The selected physical frame, source label, and one resolution group stay aligned, including guards belonging to intervening IF frames.

Main declarations: `FramePlans.before_mark`. A direct consumer is `Compiler.Body.Control.Control.CumulativePointControl`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A future plan after recording a forward branch yields the corresponding
plan before it. The selected physical frame, source label, and one resolution
group stay aligned, including guards belonging to intervening IF frames. -/
theorem FramePlans.before_mark {length locals updated labels groups}
    (plans : FramePlans length locals updated labels groups)
    {original : List runtime.compiler.Frame} {index depth : Nat} {frame : runtime.compiler.Frame}
    (fixups : alloc.vec.Vec Usize)
    (replacement : updated = original.set index {frame with end_reachable := true, fixups})
    (found : original[index]? = some frame)
    (position : index + depth + 1 = original.length) :
    ∃ label before after, labels[depth]? = some label ∧ label.branchLive = true ∧
      FramePlans length locals original labels (before ++ ⟨frame.fixups.val, label.target⟩ :: after) ∧
      groups = before ++ ⟨fixups.val, label.target⟩ :: after := by
  induction plans generalizing original index depth with
  | nil =>
    have size := congrArg List.length replacement
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.length_nil, List.length_set] at size
    omega
  | @push frames labels groups prior top label guardTarget future ih =>
    rcases List.eq_nil_or_concat original with empty | ⟨initial, last, originalEq⟩
    · simp [empty] at found
    · rw [List.concat_eq_append] at originalEq
      subst original
      have lengths : frames.length = initial.length := by
        have size := congrArg List.length replacement
        simp only [List.length_set, List.length_append, List.length_singleton] at size
        omega
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at bound position
      by_cases atTop : index = initial.length
      · have sameFrame : last = frame := by simpa [atTop] using found
        subst last
        have zero : depth = 0 := by omega
        have replaced : frames ++ [top] = initial ++ [{frame with end_reachable := true, fixups}] := by
          simpa [atTop, List.set_append_right, Nat.le_refl] using replacement
        obtain ⟨sameInitial, sameTop⟩ := List.append_inj replaced lengths
        simp only [List.cons.injEq, and_true] at sameTop
        subst initial top
        refine ⟨label, (match frame.if_pc with | none => [] | some site => [⟨[site], guardTarget⟩]), groups,
          by simp [zero], future.marked rfl, ?_, ?_⟩
        · have planned := FramePlans.push prior frame label guardTarget
            (FrameFuture.previous_mark (frame := frame) (fixups := fixups) future)
          convert planned using 1 <;> simp [frameGroups, List.append_assoc] <;> rfl
        · simp [frameGroups, List.append_assoc]
          <;> rfl
      · have inside : index < initial.length := by omega
        have positive : 0 < depth := by omega
        have replaced : frames ++ [top] =
            initial.set index {frame with end_reachable := true, fixups} ++ [last] := by
          simpa only [List.set_append_left index _ inside] using replacement
        obtain ⟨sameInitial, sameTop⟩ := List.append_inj replaced (by simpa using lengths)
        simp only [List.cons.injEq, and_true] at sameTop
        subst top
        obtain ⟨chosen, before, after, labelAt, live, previous, grouped⟩ := ih sameInitial
          (by simpa only [List.getElem?_append_left inside] using found)
          (depth := depth - 1) (by omega)
        refine ⟨chosen, frameGroups last label guardTarget ++ before, after, ?_, live, ?_, ?_⟩
        · have decomp : depth = (depth - 1) + 1 := by omega
          rw [decomp, List.getElem?_cons_succ]
          exact labelAt
        · simpa only [List.append_assoc] using FramePlans.push previous last label guardTarget future
        · simp only [grouped, List.append_assoc]

end Itasca.Runtime.Compiler

end

/-! ## FixupBudget -/

section

/-!
At a complete callback boundary, each retained fixup was paid for by an emitted branch. Address validity alone does not imply this allocation bound.

Main declarations: `FixupBudget`. A direct consumer is `Compiler.Local.Callbacks.Fixups.FixupPreservation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- At a complete callback boundary, each retained fixup was paid for by an
emitted branch. Address validity alone does not imply this allocation bound. -/
def FixupBudget (frames : List runtime.compiler.Frame) (codeLength : Nat) : Prop :=
  ∀ frame ∈ frames, frame.fixups.val.length ≤ codeLength

theorem FixupBudget.mono {frames before after} (budget : FixupBudget frames before)
    (growth : before ≤ after) : FixupBudget frames after :=
  fun frame member => (budget frame member).trans growth

theorem FixupBudget.empty (codeLength : Nat) : FixupBudget [] codeLength := by
  simp [FixupBudget]

theorem FixupBudget.push {frames codeLength} (budget : FixupBudget frames codeLength)
    (frame : runtime.compiler.Frame) (fresh : frame.fixups.val = []) :
    FixupBudget (frames ++ [frame]) codeLength := by
  intro f member
  rcases List.mem_append.mp member with old | last
  · exact budget f old
  · simp only [List.mem_singleton] at last
    subst f
    simp [fresh]

theorem FixupBudget.set {frames codeLength} (budget : FixupBudget frames codeLength)
    (index : Nat) (replacement : runtime.compiler.Frame)
    (bound : replacement.fixups.val.length ≤ codeLength) :
    FixupBudget (frames.set index replacement) codeLength := by
  induction frames generalizing index with
  | nil => exact .empty _
  | cons frame rest ih =>
    cases index with
    | zero =>
      intro f member
      simp only [List.set_cons_zero, List.mem_cons] at member
      rcases member with rfl | old
      · exact bound
      · exact budget f (List.mem_cons_of_mem _ old)
    | succ index =>
      intro f member
      simp only [List.set_cons_succ, List.mem_cons] at member
      rcases member with rfl | tail
      · exact budget f (by simp)
      · exact ih (fun f member => budget f (List.mem_cons_of_mem _ member)) index f tail

theorem FixupBudget.branch {frames before after} (budget : FixupBudget frames before)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (selected : frames[index]? = some frame)
    (appended : fixups.val.length = frame.fixups.val.length + 1)
    (growth : before + 1 ≤ after) :
    FixupBudget (frames.set index {frame with end_reachable := true, fixups}) after := by
  apply (budget.mono (by omega)).set
  have old := budget frame (List.mem_of_getElem? selected)
  simp only
  omega

theorem FixupBudget.lookup {frames codeLength} (budget : FixupBudget frames codeLength)
    {index : Nat} {frame : runtime.compiler.Frame} (selected : frames[index]? = some frame) (capacity : codeLength < Usize.max) :
    frame.fixups.val.length < Usize.max :=
  (budget frame (List.mem_of_getElem? selected)).trans_lt capacity

end Itasca.Runtime.Compiler

end
