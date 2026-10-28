import Exec.Code.Local.Callbacks.Common.OpenPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A possible static completion of one physical open frame. Future normal
liveness is unrestricted; previously observed branches must remain live.
Loop branch targets are already fixed, while forward exits stay beyond the
currently emitted prefix. This predicate contains no machine execution claim. -/
structure FrameFuture (length : Nat) (locals : List valtype)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32) : Prop where
  height : frame.entry_reachable = true → frame.height.val = slots locals + slots label.front
  results : frame.entry_reachable = true → frame.results.val = slots label.resultTypes
  branchWidth : frame.entry_reachable = true →
    (match frame.kind with | .Loop => frame.params.val | _ => frame.results.val) = slots label.branchTypes
  normalBound : length ≤ label.normalExit
  forwardBound : frame.kind ≠ .Loop → length ≤ label.target.val
  loopTarget : frame.kind = .Loop → label.target = frame.start_pc
  loopLive : frame.kind = .Loop → label.branchLive = true
  marked : frame.end_reachable = true → label.branchLive = true
  sharedExit : frame.kind ≠ .Loop → frame.kind ≠ .Then → label.normalExit = label.target.val
  guardBound : frame.if_pc.isSome = true → length ≤ guardTarget.val

theorem FrameFuture.before {length smaller locals frame label guardTarget}
    (future : FrameFuture length locals frame label guardTarget) (order : smaller ≤ length) :
    FrameFuture smaller locals frame label guardTarget :=
  { future with normalBound := order.trans future.normalBound, forwardBound := fun h => order.trans (future.forwardBound h), guardBound := fun h => order.trans (future.guardBound h) }

/-- A plan admissible after recording a branch was already admissible before
that branch; the prior universally quantified prefix can use it unchanged. -/
theorem FrameFuture.previous_mark {length locals frame label guardTarget fixups}
    (future : FrameFuture length locals {frame with end_reachable := true, fixups} label guardTarget) :
    FrameFuture length locals frame label guardTarget :=
  { future with marked := fun _ => future.marked rfl }

/-- A THEN guard and its body's forward branches are distinct resolution
roles, even though they share a physical control frame. -/
def frameGroups (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32) :
    List FixupTarget :=
  (match frame.if_pc with | none => [] | some site => [⟨[site], guardTarget⟩]) ++
    [⟨frame.fixups.val, label.target⟩]

/-- Plans follow the compiler's outer-to-inner physical frame vector while
static labels and resolution groups are kept in nearest-label-first order. -/
inductive FramePlans (length : Nat) (locals : List valtype) :
    List runtime.compiler.Frame → List LabelTarget → List FixupTarget → Prop where
  | nil : FramePlans length locals [] [] []
  | push {frames labels groups} (prior : FramePlans length locals frames labels groups)
      (frame label guardTarget) (future : FrameFuture length locals frame label guardTarget) :
      FramePlans length locals (frames ++ [frame]) (label :: labels)
        (frameGroups frame label guardTarget ++ groups)

theorem FramePlans.before {length smaller locals frames labels groups}
    (plans : FramePlans length locals frames labels groups) (order : smaller ≤ length) :
    FramePlans smaller locals frames labels groups := by
  induction plans with
  | nil => exact .nil
  | push prior frame label guardTarget future ih =>
    exact .push ih frame label guardTarget (future.before order)

theorem FramePlans.lookup {length locals frames labels groups}
    (plans : FramePlans length locals frames labels groups) {index depth : Nat} {frame}
    (atFrame : frames[index]? = some frame) (position : index + depth + 1 = frames.length) :
    ∃ label guardTarget, labels[depth]? = some label ∧ FrameFuture length locals frame label guardTarget := by
  induction plans generalizing index depth with
  | nil => simp at atFrame
  | @push frames labels groups prior current label guardTarget future ih =>
    by_cases top : index = frames.length
    · have zero : depth = 0 := by simp only [List.length_append, List.length_singleton] at position; omega
      have same : frame = current := by simpa [top] using atFrame.symm
      subst frame
      exact ⟨label, guardTarget, by simp [zero], future⟩
    · have inside : index < frames.length := by
        have bound := (List.getElem?_eq_some_iff.mp atFrame).1
        simp only [List.length_append, List.length_singleton] at bound
        omega
      have positive : 0 < depth := by simp only [List.length_append, List.length_singleton] at position; omega
      obtain ⟨found, target, lookup, valid⟩ := ih
        (by simpa only [List.getElem?_append_left inside] using atFrame)
        (depth := depth - 1) (by simp only [List.length_append, List.length_singleton] at position; omega)
      refine ⟨found, target, ?_, valid⟩
      have decomp : depth = (depth - 1) + 1 := by omega
      rw [decomp, List.getElem?_cons_succ]
      exact lookup

end Itasca.Runtime.Code
