import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalInitial
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSource
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
