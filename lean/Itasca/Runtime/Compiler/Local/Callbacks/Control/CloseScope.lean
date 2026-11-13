import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalInitial
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf

/-!
Sections, each formerly its own module: ScopeConditions, ScopeFrame, ScopeFramePatch, ScopeFrameGuard, ScopeFrameElse, ScopeNesting, ScopeFrameStack, CloseScope.
-/

/-! ## ScopeConditions -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The saved IF condition occupies the word immediately above its parameters.
Its exact coordinate is retained while either arm is compiled. -/
def ScopeCondition (locals : List valtype) (scope : SourceScope) : Prop :=
  match scope.form with
  | .then_ _ condition | .else_ _ condition _ _ _ _ =>
      scope.entered = true → condition.val = slots locals + slots scope.input
  | _ => True

def ScopeConditions (locals : List valtype) (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ scope ∈ parents ++ [current], ScopeCondition locals scope

theorem ScopeCondition.advance {locals scope} (condition : ScopeCondition locals scope)
    (instruction : instr) : ScopeCondition locals (scope.advance instruction) := condition

theorem ScopeCondition.begin_else {locals scope} (condition : ScopeCondition locals scope)
    (bt : blocktype) (operand : U32) (form : scope.form = .then_ bt operand)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ScopeCondition locals (scope.begin_else bt operand yesExit noEntry normal) := by
  simpa only [ScopeCondition, form, SourceScope.begin_else, SourceScope.input] using condition

theorem ScopeConditions.current {locals parents current} (conditions : ScopeConditions locals parents current) :
    ScopeCondition locals current := conditions current (by simp)

theorem ScopeConditions.replace_current {locals parents current}
    (conditions : ScopeConditions locals parents current) (next : SourceScope) (condition : ScopeCondition locals next) :
    ScopeConditions locals parents next := by
  intro scope member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact conditions scope (List.mem_append_left _ member)
  · exact condition

theorem ScopeConditions.advance {locals parents current} (conditions : ScopeConditions locals parents current)
    (instruction : instr) : ScopeConditions locals parents (current.advance instruction) :=
  conditions.replace_current _ (conditions.current.advance instruction)

theorem ScopeConditions.begin_else {locals parents current} (conditions : ScopeConditions locals parents current)
    (bt : blocktype) (operand : U32) (form : current.form = .then_ bt operand)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ScopeConditions locals parents (current.begin_else bt operand yesExit noEntry normal) :=
  conditions.replace_current _ (conditions.current.begin_else bt operand form yesExit noEntry normal)

theorem ScopeConditions.push {locals parents current} (conditions : ScopeConditions locals parents current)
    (child : SourceScope) (condition : ScopeCondition locals child) :
    ScopeConditions locals (parents ++ [current]) child := by
  intro scope member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (old | rfl) | rfl
  · exact conditions scope (by simp [old])
  · exact conditions.current
  · exact condition

theorem ScopeConditions.pop {locals parents parent current}
    (conditions : ScopeConditions locals (parents ++ [parent]) current) : ScopeConditions locals parents parent := by
  intro scope member
  exact conditions scope (List.mem_append_left _ member)

theorem ScopeConditions.initial {locals returns} : ScopeConditions locals [] (SourceScope.initial returns) := by
  intro scope member
  simp only [List.nil_append, List.mem_singleton] at member
  subst scope
  trivial

end Itasca.Runtime.Compiler

end

/-! ## ScopeFrame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The IF frame starts after its guard. Other fresh frames start at entry. -/
def SourceScope.frameStart (scope : SourceScope) : Nat :=
  scope.entry + match scope.form with
    | .then_ _ _ | .else_ _ _ _ _ _ _ => if scope.entered then 1 else 0
    | _ => 0

/-- LOOP and IF consume one instruction at entry only when entered. -/
def SourceScope.bodyStart (scope : SourceScope) : Nat :=
  match scope.form with
  | .loop _ | .then_ _ _ => scope.entry + (if scope.entered then 1 else 0)
  | .else_ _ _ _ _ noEntry _ => noEntry.val
  | _ => scope.entry

def SourceScope.guardPosition (scope : SourceScope) : Option Nat :=
  match scope.form with
  | .then_ _ _ => if scope.entered then some scope.entry else none
  | _ => none

/-- Physical label metadata follows the exact source scope, including dormant
subtrees whose operand-stack height is not a live layout obligation. -/
structure ScopeFrameShape (locals : List valtype) (scope : SourceScope)
    (frame : runtime.compiler.Frame) : Prop where
  kind : frame.kind = scope.form.kind
  entered : frame.entry_reachable = scope.entered
  params : frame.params.val = slots scope.params
  results : frame.results.val = slots scope.results
  height : scope.entered = true → frame.height.val = slots locals + slots scope.front
  start : frame.start_pc.val = scope.frameStart
  body : scope.bodyPc = scope.bodyStart
  guard : frame.if_pc.map UScalar.val = scope.guardPosition
  root : scope.form = .body → scope.entry = 0
  loopClean : ∀ bt, scope.form = .loop bt → frame.fixups.val = [] ∧ frame.end_reachable = false
  elseLive : ∀ bt condition yes yesExit noEntry normal,
    scope.form = .else_ bt condition yes yesExit noEntry normal →
    normal = true → frame.end_reachable = true

/-- Code retained by an open frame consists of its LOOP hook or unresolved IF
guard; ordinary forward branch holes are tracked separately by FrameSites. -/
def ScopeEntryCode (code : List Bytecode) (scope : SourceScope) : Prop :=
  match scope.form with
  | .loop _ => scope.entered = true → code[scope.entry]? = some .LoopHead
  | .then_ _ condition => scope.entered = true →
      code[scope.entry]? = some (.JumpIfZero condition core.num.U32.MAX)
  | _ => True

structure FrameScope {A : Type} (locals : List valtype)
    (compiler : runtime.compiler.FunctionCompiler A) (scope : SourceScope)
    (frame : runtime.compiler.Frame) : Prop extends ScopeFrameShape locals scope frame where
  mapBound : frame.map.val < compiler.function.controls.val.length
  entryBound : scope.entry ≤ compiler.function.code.val.length
  bodyBound : scope.bodyPc ≤ compiler.function.code.val.length
  entryCode : ScopeEntryCode compiler.function.code.val scope

theorem ScopeFrameShape.advance {locals scope frame} (shape : ScopeFrameShape locals scope frame)
    (instruction : instr) : ScopeFrameShape locals (scope.advance instruction) frame :=
  ⟨shape.kind, shape.entered, shape.params, shape.results, shape.height, shape.start,
    shape.body, shape.guard, shape.root, shape.loopClean, shape.elseLive⟩

theorem FrameScope.advance {A : Type} {locals} {compiler : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals compiler scope frame) (instruction : instr) :
    FrameScope locals compiler (scope.advance instruction) frame :=
  ⟨shape.toScopeFrameShape.advance instruction, shape.mapBound, shape.entryBound,
    shape.bodyBound, shape.entryCode⟩

/-- Metadata and retained entry instructions suffice to transport alignment. -/
theorem FrameScope.transport {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length)
    (code : before.function.code.val.length ≤ after.function.code.val.length)
    (entryCode : ScopeEntryCode after.function.code.val scope) : FrameScope locals after scope frame :=
  ⟨shape.toScopeFrameShape, shape.mapBound.trans_le maps, shape.entryBound.trans code,
    shape.bodyBound.trans code, entryCode⟩

theorem ScopeEntryCode.extend {code scope} (entry : ScopeEntryCode code scope) (suffix : List Bytecode) :
    ScopeEntryCode (code ++ suffix) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  all_goals intro live
  all_goals exact fetch_extend (entry live) suffix

theorem FrameScope.extend {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame) (suffix : List Bytecode)
    (code : after.function.code.val = before.function.code.val ++ suffix)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code]
  · simpa only [code] using shape.entryCode.extend suffix

/-- The actual root frame has no guard or pending branch sites at entry. -/
theorem FrameScope.initial {A : Type} (locals returns : List valtype)
    (compiler : runtime.compiler.FunctionCompiler A) (localSlots resultSlots : U32)
    (localWidth : localSlots.val = slots locals) (resultWidth : resultSlots.val = slots returns)
    (mapPresent : 0 < compiler.function.controls.val.length) :
    FrameScope locals compiler (SourceScope.initial returns)
      ⟨0#usize, .Body, localSlots, 0#u32, resultSlots, 0#u32, none, true, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp [SourceScope.initial, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition, slots, localWidth, resultWidth]
  · exact mapPresent
  · simp [SourceScope.initial]
  · simp [SourceScope.initial]
  · trivial
end Itasca.Runtime.Compiler

end

/-! ## ScopeFramePatch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Forward branch fixups cannot overwrite a LOOP hook or an open IF guard. -/
theorem ScopeEntryCode.patch_branches {code scope sites}
    (entry : ScopeEntryCode code scope) (branches : ForwardSites code sites) (target : U32) :
    ScopeEntryCode (patchCode code sites target) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  · intro live
    have found := entry live
    rw [patch_code_get]
    split
    · simp [found, retarget]
    · exact found
  · intro live
    have found := entry live
    rw [patch_code_other code sites target scope.entry (fun site member => (branches.not_guard found site member).symm)]
    exact found

/-- Closing a child changes parent code targets while retaining parent entry geometry. -/
theorem FrameScope.patch_branches {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame sites} (shape : FrameScope locals before scope frame)
    (branches : ForwardSites before.function.code.val sites) (target : U32)
    (code : after.function.code.val = patchCode before.function.code.val sites target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code, patch_code_length]
  · simpa only [code] using shape.entryCode.patch_branches branches target
end Itasca.Runtime.Compiler

end

/-! ## ScopeFrameGuard -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Resolving another frame's IF guard preserves this scope's entry instruction. -/
theorem ScopeEntryCode.set_guard {code scope} (entry : ScopeEntryCode code scope)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (distinct : scope.guardPosition ≠ some guard.val) :
    ScopeEntryCode (code.set guard.val (.JumpIfZero condition target)) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  · intro live
    have atEntry := entry live
    have away : guard.val ≠ scope.entry := by
      intro equal
      rw [equal, atEntry] at found
      cases found
    rw [List.getElem?_set_ne away]
    exact atEntry
  · intro live
    have away : guard.val ≠ scope.entry := by
      intro equal
      apply distinct
      simp_all [SourceScope.guardPosition]
    rw [List.getElem?_set_ne away]
    exact entry live

end Itasca.Runtime.Compiler

end

/-! ## ScopeFrameElse -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- ELSE keeps the original frame signature and stack base, consumes its guard,
and starts the second arm at the resolved destination. -/
theorem ScopeFrameShape.begin_else {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (bt : blocktype) (condition : U32)
    (form : scope.form = .then_ bt condition) (yesExit : Nat) (noEntry : U32)
    (normal : Bool) (fixups : alloc.vec.Vec Usize) :
    ScopeFrameShape locals (scope.begin_else bt condition yesExit noEntry normal)
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} := by
  refine ⟨rfl, shape.entered, shape.params, shape.results, shape.height, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · change frame.start_pc.val = scope.entry + (if scope.entered then 1 else 0)
    have start := shape.start
    unfold SourceScope.frameStart at start
    rw [form] at start
    exact start
  · simp [SourceScope.begin_else]
  · simp [SourceScope.begin_else]
  · cases normal <;> simp [SourceScope.begin_else]

theorem FrameScope.begin_else {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame) (bt : blocktype) (condition : U32)
    (form : scope.form = .then_ bt condition) (yesExit : Nat) (noEntry : U32)
    (normal : Bool) (fixups : alloc.vec.Vec Usize)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length)
    (code : before.function.code.val.length ≤ after.function.code.val.length)
    (bodyBound : noEntry.val ≤ after.function.code.val.length) :
    FrameScope locals after (scope.begin_else bt condition yesExit noEntry normal)
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} := by
  exact ⟨shape.toScopeFrameShape.begin_else bt condition form yesExit noEntry normal fixups,
    shape.mapBound.trans_le maps, shape.entryBound.trans code, bodyBound, trivial⟩

/-- Recording a forward branch changes only its target frame's fixup list and
exit liveness. Loop targets are handled separately and never record fixups. -/
theorem ScopeFrameShape.record_branch {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (fixups : alloc.vec.Vec Usize)
    (forward : frame.kind ≠ .Loop) :
    ScopeFrameShape locals scope {frame with fixups, end_reachable := true} := by
  refine ⟨shape.kind, shape.entered, shape.params, shape.results, shape.height,
    shape.start, shape.body, shape.guard, shape.root, ?_, by simp⟩
  intro bt form
  have kind := shape.kind
  simp only [form, ScopeForm.kind] at kind
  exact (forward kind).elim

theorem FrameScope.record_branch {A : Type} {locals} {compiler : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals compiler scope frame) (fixups : alloc.vec.Vec Usize)
    (forward : frame.kind ≠ .Loop) :
    FrameScope locals compiler scope {frame with fixups, end_reachable := true} :=
  ⟨shape.toScopeFrameShape.record_branch fixups forward, shape.mapBound, shape.entryBound,
    shape.bodyBound, shape.entryCode⟩
end Itasca.Runtime.Compiler

end

/-! ## ScopeNesting -/

section

/-!
Source-scope entry forms and their nesting geometry. ScopeNesting gives ancestor bounds needed by control-map and frame-stack proofs.
-/

/-! ## Scope Frame Enter -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def SourceScope.enterBlock (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.block bt, front, params, results, [], entry, entry, entered⟩

def SourceScope.enterLoop (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.loop bt, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

def SourceScope.enterIf (bt : blocktype) (condition : U32) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.then_ bt condition, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

/-- The exact freshly pushed BLOCK frame matches its new source scope. -/
theorem FrameScope.enter_block {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val ≤ compiler.function.code.val.length) :
    FrameScope locals compiler (SourceScope.enterBlock bt front params results pc.val entered)
      ⟨map, .Block, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterBlock, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · exact position
  · exact position
  · trivial

/-- A freshly pushed LOOP retains its hook only when source entry was live. -/
theorem FrameScope.enter_loop {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length)
    (hook : entered = true → compiler.function.code.val[pc.val]? = some .LoopHead) :
    FrameScope locals compiler (SourceScope.enterLoop bt front params results pc.val entered)
      ⟨map, .Loop, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterLoop, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition, alloc.vec.Vec.new]
  · exact mapBound
  · change pc.val ≤ compiler.function.code.val.length
    omega
  · exact position
  · exact hook

/-- An entered IF owns a fresh guard immediately before its frame's start PC. -/
theorem FrameScope.enter_if {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (condition : U32) (map entry : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (start : pc.val = entry.val + (if entered then 1 else 0))
    (position : pc.val ≤ compiler.function.code.val.length)
    (guard : entered = true → compiler.function.code.val[entry.val]? = some (.JumpIfZero condition core.num.U32.MAX)) :
    FrameScope locals compiler (SourceScope.enterIf bt condition front params results entry.val entered)
      ⟨map, .Then, height, paramWidth, resultWidth, pc, (if entered then some entry else none),
        entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterIf, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · change entry.val ≤ compiler.function.code.val.length
    omega
  · change entry.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length
    omega
  · exact guard
end Itasca.Runtime.Compiler

end

/-! ## Scope Nesting -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Nested source scopes begin after their parent's body entry. The extra local
geometry also covers ELSE scopes, whose body begins at a patched destination. -/
inductive ScopeNesting : List SourceScope → SourceScope → Prop
  | root (scope : SourceScope) (geometry : scope.entry ≤ scope.bodyPc) : ScopeNesting [] scope
  | push {parents parent} (outer : ScopeNesting parents parent) (child : SourceScope)
      (order : parent.bodyPc ≤ child.entry) (geometry : child.entry ≤ child.bodyPc) :
      ScopeNesting (parents ++ [parent]) child

theorem ScopeNesting.geometry {parents current} (nested : ScopeNesting parents current) :
    current.entry ≤ current.bodyPc := by
  cases nested <;> assumption

theorem ScopeNesting.ancestor_bound {parents current} (nested : ScopeNesting parents current)
    (scope : SourceScope) (member : scope ∈ parents) : scope.bodyPc ≤ current.entry := by
  induction nested with
  | root => simp at member
  | @push parents parent outer child order geometry ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact (ih member).trans (outer.geometry.trans order)
    · exact order

theorem ScopeNesting.change_current {parents current} (nested : ScopeNesting parents current)
    (next : SourceScope) (entry : next.entry = current.entry)
    (geometry : next.entry ≤ next.bodyPc) : ScopeNesting parents next := by
  cases nested with
  | root => exact .root next geometry
  | push outer child order oldGeometry => exact .push outer next (by simpa [entry] using order) geometry

theorem ScopeNesting.advance {parents current} (nested : ScopeNesting parents current)
    (instruction : instr) : ScopeNesting parents (current.advance instruction) :=
  nested.change_current _ rfl nested.geometry

theorem ScopeNesting.pop {parents parent child}
    (nested : ScopeNesting (parents ++ [parent]) child) : ScopeNesting parents parent := by
  generalize equation : parents ++ [parent] = allParents at nested
  cases nested with
  | root => simp at equation
  | @push outerParents outerParent outer current order geometry =>
    have same : parents = outerParents ∧ parent = outerParent := by simpa using equation
    rcases same with ⟨rfl, rfl⟩
    exact outer

theorem ScopeNesting.initial (returns : List valtype) : ScopeNesting [] (SourceScope.initial returns) :=
  .root _ (by simp [SourceScope.initial])

/-- A physical IF guard sits strictly before its own body. -/
theorem ScopeFrameShape.guard_geometry {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (guard : Usize)
    (found : frame.if_pc = some guard) : guard.val = scope.entry ∧ guard.val < scope.bodyPc := by
  have mapped := shape.guard
  rw [found] at mapped
  simp only [Option.map_some] at mapped
  cases form : scope.form <;> simp [SourceScope.guardPosition, form] at mapped
  rename_i bt condition
  cases entered : scope.entered <;> simp [entered] at mapped
  have body := shape.body
  simp only [SourceScope.bodyStart, form, entered, ↓reduceIte] at body
  exact ⟨mapped, by omega⟩

private theorem paired_member {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) {value : β} (member : value ∈ right) :
    ∃ item, item ∈ left ∧ R item value := by
  induction paired with
  | nil => simp at member
  | @cons a b left right related rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨a, by simp, related⟩
    · obtain ⟨item, present, related⟩ := ih member
      exact ⟨item, List.mem_cons_of_mem _ present, related⟩

/-- Guard distinctness follows from actual frame/source alignment and scope
nesting, rather than an assumption about the compiler's chosen addresses. -/
theorem ScopeNesting.distinct_guard {locals parents current frames frame}
    (nested : ScopeNesting parents current)
    (paired : List.Forall₂ (ScopeFrameShape locals) parents frames)
    (shape : ScopeFrameShape locals current frame) (guard : Usize)
    (found : frame.if_pc = some guard) : ∀ other ∈ frames, other.if_pc ≠ some guard := by
  intro other member same
  obtain ⟨scope, present, otherShape⟩ := paired_member paired member
  have currentGuard := (shape.guard_geometry guard found).1
  have parentGuard := (otherShape.guard_geometry guard same).2
  have ordered := nested.ancestor_bound scope present
  omega
theorem ScopeNesting.enter_block {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterBlock bt front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterBlock])

theorem ScopeNesting.enter_loop {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterLoop bt front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterLoop])

theorem ScopeNesting.enter_if {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype) (condition : U32)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterIf bt condition front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterIf])
end Itasca.Runtime.Compiler

end

end

/-! ## ScopeFrameStack -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every physical frame is paired with its exact source scope, ordered from
outermost to innermost, with source-entry geometry retained across suspension. -/
structure ScopeFrameStack {A : Type} (locals : List valtype)
    (compiler : runtime.compiler.FunctionCompiler A) (parents : List SourceScope)
    (current : SourceScope) : Prop where
  nested : ScopeNesting parents current
  frames : List.Forall₂ (FrameScope locals compiler) (parents ++ [current]) compiler.frames.val

private theorem paired_last {α β : Type} {R : α → β → Prop} {left right value}
    (same : List.Forall₂ R left (right ++ [value])) :
    ∃ beginning item, left = beginning ++ [item] ∧ List.Forall₂ R beginning right ∧ R item value := by
  have beginning := List.forall₂_take_append left right [value] same
  have ending := List.forall₂_drop_append left right [value] same
  have singleton : ∀ {items : List α}, List.Forall₂ R items [value] → ∃ item, items = [item] ∧ R item value := by
    intro items related
    cases related with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨item, rest, related⟩ := singleton ending
  exact ⟨left.take right.length, item, by rw [← rest, List.take_append_drop], beginning, related⟩

private theorem paired_imp_member {α β : Type} {R S : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right)
    (change : ∀ a b, b ∈ right → R a b → S a b) : List.Forall₂ S left right := by
  induction paired with
  | nil => exact .nil
  | @cons a b left right related rest ih =>
    exact .cons (change a b (by simp) related)
      (ih (fun a b member related => change a b (List.mem_cons_of_mem _ member) related))

theorem ScopeFrameStack.split {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current) :
    ∃ prior frame, compiler.frames.val = prior ++ [frame] ∧
      List.Forall₂ (FrameScope locals compiler) parents prior ∧ FrameScope locals compiler current frame := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := paired_last (List.Forall₂.flip stack.frames)
  exact ⟨prior, frame, frames, List.Forall₂.flip paired, shape⟩

theorem ScopeFrameStack.transport {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (frames : after.frames.val = before.frames.val)
    (preserve : ∀ scope frame, FrameScope locals before scope frame → FrameScope locals after scope frame) :
    ScopeFrameStack locals after parents current := by
  refine ⟨stack.nested, ?_⟩
  rw [frames]
  exact stack.frames.imp preserve

theorem ScopeFrameStack.extend {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (frames : after.frames.val = before.frames.val) (suffix : List Bytecode)
    (code : after.function.code.val = before.function.code.val ++ suffix)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents current :=
  stack.transport frames (fun _ _ shape => shape.extend suffix code maps)

theorem ScopeFrameStack.advance {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (instruction : instr) : ScopeFrameStack locals compiler parents (current.advance instruction) := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := stack.split
  refine ⟨stack.nested.advance instruction, ?_⟩
  rw [frames]
  exact List.rel_append paired (.cons (shape.advance instruction) .nil)

theorem ScopeFrameStack.push {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = before.frames.val ++ [frame])
    (preserve : ∀ scope oldFrame, FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame)
    (fresh : FrameScope locals after child frame) (order : current.bodyPc ≤ child.entry)
    (geometry : child.entry ≤ child.bodyPc) :
    ScopeFrameStack locals after (parents ++ [current]) child := by
  refine ⟨.push stack.nested child order geometry, ?_⟩
  rw [frames]
  exact List.rel_append (stack.frames.imp preserve) (.cons fresh .nil)

/-- Closing the inner frame restores its paired parent and its source geometry. -/
theorem ScopeFrameStack.pop {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (frames : before.frames.val = after.frames.val ++ [frame])
    (preserve : ∀ scope oldFrame, oldFrame ∈ after.frames.val →
      FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame) :
    ScopeFrameStack locals after parents parent := by
  obtain ⟨prior, currentFrame, split, paired, shape⟩ := stack.split
  have same : prior = after.frames.val ∧ currentFrame = frame := by
    simpa using split.symm.trans frames
  rw [same.1] at paired
  exact ⟨stack.nested.pop, paired_imp_member paired preserve⟩

theorem ScopeFrameStack.distinct_guard {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame]) (guard : Usize) (found : frame.if_pc = some guard) :
    ∀ other ∈ prior, other.if_pc ≠ some guard := by
  obtain ⟨actualPrior, actualFrame, actualFrames, paired, shape⟩ := stack.split
  have equal : actualPrior = prior ∧ actualFrame = frame := by
    simpa using actualFrames.symm.trans frames
  rcases equal with ⟨rfl, rfl⟩
  exact stack.nested.distinct_guard (paired.imp (fun _ _ h => h.toScopeFrameShape))
    shape.toScopeFrameShape guard found
theorem ScopeFrameStack.initial {A : Type} {locals returns}
    {compiler : runtime.compiler.FunctionCompiler A} (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = [frame])
    (shape : FrameScope locals compiler (SourceScope.initial returns) frame) :
    ScopeFrameStack locals compiler [] (SourceScope.initial returns) := by
  refine ⟨.initial returns, ?_⟩
  rw [frames]
  exact .cons shape .nil

/-- Replace the active frame after transporting its suspended ancestors. This
covers ELSE, whose new body entry is later but whose source entry is unchanged. -/
theorem ScopeFrameStack.replace_current {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (next : SourceScope) (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = prior ++ [frame])
    (retained : List.Forall₂ (FrameScope locals after) parents prior)
    (fresh : FrameScope locals after next frame) (entry : next.entry = current.entry)
    (geometry : next.entry ≤ next.bodyPc) : ScopeFrameStack locals after parents next := by
  refine ⟨stack.nested.change_current next entry geometry, ?_⟩
  rw [frames]
  exact List.rel_append retained (.cons fresh .nil)
private theorem paired_set_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (before after : β)
    (found : right[index]? = some before) (change : ∀ a, R a before → R a after) :
    List.Forall₂ R left (right.set index after) := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right related rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst b
      exact .cons (change a related) rest
    | succ index => exact .cons related (ih index found)

/-- Recording a branch changes only its selected forward frame's fixups and
exit liveness; its source scope and nesting geometry remain paired. -/
theorem ScopeFrameStack.record_branch {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (frames : after.frames.val = before.frames.val.set index {frame with fixups, end_reachable := true})
    (preserve : ∀ scope oldFrame, FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame) :
    ScopeFrameStack locals after parents current := by
  refine ⟨stack.nested, ?_⟩
  rw [frames]
  exact paired_set_right (stack.frames.imp preserve) index frame _ found
    (fun _ shape => shape.record_branch fixups forward)
end Itasca.Runtime.Compiler

end

/-! ## CloseScope -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
/-- Reachability restored by END, including the implicit empty else arm. -/
def scopeExitLive (reachable : Bool) (frame : runtime.compiler.Frame) : Bool :=
  reachable || frame.end_reachable || (match frame.kind with | .Then => frame.entry_reachable | _ => false)

@[step] theorem close_scope_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (nonBody : frame.kind ≠ .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = scopeExitLive compiler.reachable frame ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ∧
        ∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, noIf]
  step with compiler_fixups ops { compiler with frames := rest } frame.fixups target 0#usize
    (by simp) branches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) = .ok (frame.kind, scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases reach : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive, kind, reach, ends, bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) _) _
  rw [choice, bind_ok]
  have notBody : (match frame.kind with
      | .Body => (.ok true : Result Bool)
      | .Block | .Loop | .Then | .Else => .ok false) = .ok false := by
    cases kind : frame.kind <;> simp_all
  change WP.spec (Aeneas.Std.bind (match frame.kind with
    | .Body => (.ok true : Result Bool)
    | .Block | .Loop | .Then | .Else => .ok false) _) _
  rw [notBody, bind_ok]
  simp only [Bool.false_eq_true, ite_false]
  step with compiler_observe ops law _ state as ⟨out, hout, success⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := hout success
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hframes
  · simpa using hr
  · simpa [hcode] using effect
  · refine ⟨{ map with source_end := coordinate, end_pc := pcword }, ?_, ?_, hcoordinate⟩
    · rw [hcontrols, hback]
      simp [alloc.vec.Vec.set_val_eq, mapFits]
    · rw [hpcword]
      scalar_tac


end Itasca.Runtime.Compiler

end
