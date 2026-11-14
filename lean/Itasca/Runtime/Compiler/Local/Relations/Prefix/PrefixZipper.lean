import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.OpenPrefix

/-!
Sections, each formerly its own module: FutureFrames, PrefixZipper.
-/

/-! ## FutureFrames -/

section

/-!
A possible static completion of one physical open frame. Future normal liveness is unrestricted; previously observed branches must remain live. Loop branch targets are already fixed, while forward exits stay beyond the currently emitted prefix. This predicate contains no machine execution claim.

Main declarations: `FrameFuture` and `frameGroups`. A direct consumer is `Compiler.Local.Relations.Prefix.PrefixZipper`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## PrefixZipper -/

section

/-!
Source control information retained while callbacks are still reading the body. ELSE remembers the completed arm and the actual skip decision.

Main declarations: `ScopeForm` and `ScopeForm.kind`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Source control information retained while callbacks are still reading the
body. ELSE remembers the completed arm and the actual skip decision. -/
inductive ScopeForm where
  | body
  | block (type : blocktype)
  | loop (type : blocktype)
  | then_ (type : blocktype) (condition : U32)
  | else_ (type : blocktype) (condition : U32) (yes : List instr)
      (yesExit : Nat) (noEntry : U32) (yesNormal : Bool)

def ScopeForm.kind : ScopeForm → Itasca.code.LabelKind
  | .body => .Body
  | .block _ => .Block
  | .loop _ => .Loop
  | .then_ _ _ => .Then
  | .else_ _ _ _ _ _ _ => .Else

structure SourceScope where
  form : ScopeForm
  front : List valtype
  params : List valtype
  results : List valtype
  source : List instr
  entry : Nat
  bodyPc : Nat
  entered : Bool

def SourceScope.input (scope : SourceScope) : List valtype := scope.front ++ scope.params

def SourceScope.arguments (scope : SourceScope) : List valtype :=
  scope.input ++ match scope.form with | .then_ _ _ | .else_ _ _ _ _ _ _ => [.I32] | _ => []

def SourceScope.branchTypes (scope : SourceScope) : List valtype :=
  match scope.form with | .loop _ => scope.params | _ => scope.results

/-- The source zipper fixes label types, while a future plan supplies only
coordinates and liveness. Equal word widths cannot substitute for these types. -/
structure ScopeLabel (scope : SourceScope) (label : LabelTarget) : Prop where
  front : label.front = scope.front
  branchTypes : label.branchTypes = scope.branchTypes
  results : label.resultTypes = scope.results

/-- A terminal suspended parent owns just the code before its child, exactly
as a live suspended parent does. No instruction in an unentered child is needed. -/
def SuspendedTerminal (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) : Prop :=
  cursor ≤ code.length ∧ DeadCodePrefix types functions returns locals (code.take cursor)
    labels before source start cursor

/-- A parent either waits for an entered child's typed result, already has a
terminal prefix, or itself belongs to an unentered source subtree. -/
def ParentPrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (parent child : SourceScope) : Prop :=
  if parent.entered then
    if child.entered then
      SuspendedPrefix types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry child.arguments
    else SuspendedTerminal types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry
  else True

/-- The saved parent chain mirrors the source validator zipper. Each parent
owns its prefix before the next child's opening instruction. -/
inductive ParentPrefixes (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → SourceScope → Prop where
  | root (current) : ParentPrefixes types functions returns locals code [] [] current
  | push {parents labels parent} (prior : ParentPrefixes types functions returns locals code parents labels parent)
      (label child) (shape : ScopeLabel parent label)
      (bound : child.entry ≤ code.length)
      (saved : ParentPrefix types functions returns locals code (label :: labels) parent child) :
      ParentPrefixes types functions returns locals code (parents ++ [parent]) (label :: labels) child

end Itasca.Runtime.Compiler

end
