import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FinishContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts

open WebAssembly

/-!
Proofs for Runtime / Compiler / Local / Callbacks / Control.

This module collects ElseFrames, DormantEntry.
Each section documents its contracts and consumers.
-/

/-! ## ElseFrames -/

section

open Itasca.Representation

/-! ## ElseEvidence -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- An ELSE scope retains its completed then arm, resolved guard, and literal
skip shape. Future branch liveness may overapproximate branches in the then arm;
normal liveness remains the actual decision recorded when ELSE was entered. -/
def ElseEvidence (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (outer : List LabelTarget) (scope : SourceScope) (label : LabelTarget) : Prop :=
  if scope.entered then
    match scope.form with
    | .else_ _ condition yes yesExit noEntry yesNormal =>
      condition.val = slots locals + slots scope.input ∧
      code[scope.entry]? = some (.JumpIfZero condition noEntry) ∧
      CodeRel types functions returns locals code
        (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], yesNormal, label.branchLive⟩ :: outer)
        scope.input yes (scope.entry + 1) yesExit (scope.front ++ scope.results) ∧
      IfSkip code yesExit noEntry label.target yesNormal ∧ scope.bodyPc = noEntry.val
    | _ => True
  else True

/-- Completed arms are stored at every active ELSE frame, including suspended
parents. The source and label lists are ordered from innermost to outermost. -/
inductive ElseFrames (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → Prop where
  | nil : ElseFrames types functions returns locals code [] []
  | cons {scopes labels} (scope label)
      (current : ElseEvidence types functions returns locals code labels scope label)
      (outer : ElseFrames types functions returns locals code scopes labels) :
      ElseFrames types functions returns locals code (scope :: scopes) (label :: labels)

/-- Completed-arm evidence is uniform over the same future plans as live and
terminal source prefixes. It is a separate syntactic component of the zipper. -/
def UniversalElse {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ElseFrames types functions returns locals (resolvedCode compiler.function.code.val groups)
      (current :: parents.reverse) (label :: labels)

end Itasca.Compiler

end

/-! ## ElseSource -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- The source cursor at ELSE remembers the completed then arm and resumes an
empty else body at the freshly resolved guard destination. -/
def SourceScope.begin_else (scope : SourceScope) (bt : blocktype) (condition : U32)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) : SourceScope :=
  { scope with form := .else_ bt condition scope.source yesExit noEntry normal, source := [], bodyPc := noEntry.val }

theorem SourceScope.begin_else_arguments (scope : SourceScope) (bt : blocktype) (condition : U32)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) (form : scope.form = .then_ bt condition) :
    (scope.begin_else bt condition yesExit noEntry normal).arguments = scope.arguments := by
  simp [SourceScope.begin_else, SourceScope.arguments, SourceScope.input, form]

theorem ScopeLabel.before_else {scope bt condition yesExit noEntry normal label}
    (shape : ScopeLabel (scope.begin_else bt condition yesExit noEntry normal) label)
    (form : scope.form = .then_ bt condition) : ScopeLabel scope label := by
  refine ⟨shape.front, ?_, shape.results⟩
  simpa [SourceScope.begin_else, SourceScope.branchTypes, form] using shape.branchTypes

end Itasca.Compiler

end

/-! ## ElseFrames -/

section

namespace Itasca.Compiler
open Aeneas.Std

def ScopeForm.isElse : ScopeForm → Bool
  | .else_ _ _ _ _ _ _ => true
  | _ => false

theorem ElseEvidence.fresh {types functions returns locals code labels child label}
    (fresh : child.form.isElse = false) :
    ElseEvidence types functions returns locals code labels child label := by
  unfold ElseEvidence
  split
  · cases form : child.form <;> simp_all [ScopeForm.isElse]
  · trivial

end Itasca.Compiler

end

end

/-! ## DormantEntry -/

section

open Itasca.Representation

/-!
# Dormant Entry

Dormant control entries retain source structure without requiring live emitted instructions. Their callback contracts preserve the enclosing scope invariants.
-/

/-! ## EnterDead -/

section

/-!
Compiler scope entry when the source is unreachable.

Main declarations: `enter_dead`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std
@[step] theorem enter_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code = compiler.function.code ∧
        out.2.reachable = false ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, kind, height, signature.param_slots,
              signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨kind, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  have bounds : EnterTotalBounds compiler kind := by
    refine ⟨?_, ?_, sourceFits, mapsFit, framesFit, ?_⟩
    · have bounded := pc.hmax
      scalar_tac
    · intro live
      simp only [reachable, Bool.false_eq_true] at live
    · intro live
      simp only [reachable, Bool.false_eq_true] at live
  have total := runtime.compiler.control.FunctionCompiler.enter.total ops compiler state kind bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ (Or.inl ⟨law, bounds⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists total
  rw [called, WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨priorFound, ctrlFound, sigFound, height, startPc, condition, source, middle,
    controlsFound, selectedFound, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops compiler after state kind bt (.Ok ()) called).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have signatureEq := block_signature compiler.signatures bt signature selected
  rw [selectedFound, WP.spec_ok] at signatureEq
  change sigFound = signature at signatureEq
  subst sigFound
  have publication := publish law
  have heightExact := control_stack_height_success state.vals.deref ctrl.value_stack_base
    compiler.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  simp only [alloc.vec.Vec.deref, Slice.from_val] at heightExact
  have pcEq : startPc = pc := by
    apply UScalar.eq_of_val_eq
    have start := publication.start
    simp only [enterPcAdvance, reachable] at start
    omega
  subst startPc
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have middleFrame := publication.frame
  change middle = _ at middleFrame
  rw [observedFrame]
  refine ⟨?_, ?_, height, source, heightExact, sourceEq, ?_, ?_⟩
  · apply alloc.vec.Vec.ext
    simpa only [enterPrefix, reachable, List.append_nil] using publication.code
  · rw [middleFrame]
    exact reachable
  · simpa only [enterIfPc, reachable] using publication.frames
  · exact publication.controls

end Itasca.Compiler

end

end
