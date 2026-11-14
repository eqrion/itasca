import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameStart
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic

/-!
Sections, each formerly its own module: FixupCallbacks, CallbackSafety, CallbackBounds.
-/

/-! ## FixupCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_br_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed =>
    exact budget.ordinary (compiler_observe_ordinary_result ops law before after state (.Ok ()) observed)
      (compiler_observe_code_mono ops law before after state (.Ok ()) observed)
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_fixup_budget ops law before middle depth 0#u32 false budget branched
    exact FixupBudget.ordinary (before := {middle with reachable := false}) kept (compiler_observe_ordinary_result ops law {middle with reachable := false} after state (.Ok ()) observed)
      (compiler_observe_code_mono ops law {middle with reachable := false} after state (.Ok ()) observed)

theorem compiler_br_if_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed =>
    exact budget.ordinary (compiler_observe_ordinary_result ops law before after state (.Ok ()) observed)
      (compiler_observe_code_mono ops law before after state (.Ok ()) observed)
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_fixup_budget ops law before middle depth 1#u32 true budget branched
    exact kept.ordinary (compiler_observe_ordinary_result ops law middle after state (.Ok ()) observed)
      (compiler_observe_code_mono ops law middle after state (.Ok ()) observed)

end Itasca.Runtime.Compiler

end

/-! ## CallbackSafety -/

section

/-! Raw compiler operand safety, including polymorphic bottom values. These
facts concern every normal observation outcome; they do not assume a final
accepted body or a concrete validator operand stack. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

structure ObservedStack {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (values : List Itasca.code.StackType) : Prop where
  offsets : compiler.before.val.map (fun word => word.val) =
    observedOffsets compiler.function.local_slots.val values
  height : compiler.height.val =
    compiler.function.local_slots.val + stackWords values

theorem observed_height_stack_words (height : Nat) (values : List Itasca.code.StackType) :
    observedHeight height values = height + stackWords values := by
  induction values generalizing height with
  | nil => simp [observedHeight, stackWords]
  | cons ty rest ih => simp [observedHeight, stackWords, ih, Nat.add_assoc]

theorem observed_offsets_length (height : Nat) (values : List Itasca.code.StackType) :
    (observedOffsets height values).length = values.length := by
  induction values generalizing height with
  | nil => rfl
  | cons ty rest ih => simp [observedOffsets, ih]

theorem observed_offsets_get (height : Nat) (values : List Itasca.code.StackType)
    (index : Nat) (bound : index < values.length) :
    (observedOffsets height values)[index]'(by rw [observed_offsets_length]; exact bound) =
      height + stackWords (values.take index) := by
  induction values generalizing height index with
  | nil => simp at bound
  | cons ty rest ih =>
    cases index with
    | zero => simp [observedOffsets, stackWords]
    | succ index =>
      simp only [observedOffsets, List.getElem_cons_succ, List.take_succ_cons]
      rw [ih _ _ (by simpa using bound)]
      simp [stackWords, Nat.add_assoc]

theorem ObservedStack.length {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) : compiler.before.val.length = values.length := by
  have length := congrArg List.length h.offsets
  simpa [observed_offsets_length] using length

theorem ObservedStack.get {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) (index : Nat) (bound : index < compiler.before.val.length) :
    (compiler.before.val[index]).val = compiler.function.local_slots.val +
      stackWords (values.take index) := by
  have mapped := congrArg (fun xs : List Nat => xs[index]?) h.offsets
  have vb : index < values.length := by rw [← h.length]; exact bound
  have ob : index < (observedOffsets compiler.function.local_slots.val values).length := by
    rw [observed_offsets_length]; exact vb
  have result : (compiler.before.val[index]).val =
      (observedOffsets compiler.function.local_slots.val values)[index] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some,
      List.getElem?_eq_getElem ob, Option.some.injEq] using mapped
  exact result.trans (observed_offsets_get _ _ _ vb)

theorem ObservedStack.operand_le_height {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) (index : Nat) (bound : index < compiler.before.val.length) :
    (compiler.before.val[index]).val ≤ compiler.height.val := by
  rw [h.get index bound, h.height]
  have length := h.length
  have le := stack_words_take_mono values (a := index) (b := values.length) (by omega)
  simpa using Nat.add_le_add_left le compiler.function.local_slots.val

@[step] theorem compiler_observe_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  step with compiler_observe ops law compiler state as ⟨out, observed⟩
  rename_i success
  obtain ⟨offsets, height, _, locals, _⟩ := observed success
  exact ⟨by simpa [locals] using offsets,
    by simpa [locals, observed_height_stack_words] using height⟩



end Itasca.Runtime.Compiler

end

/-! ## CallbackBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Observation bounds every prefix, including bottom-valued dormant stacks. -/
theorem ObservedStack.prefix_bound {A} {compiler : runtime.compiler.FunctionCompiler A}
    {values : List Itasca.code.StackType} (observed : ObservedStack compiler values) (count : Nat) :
    compiler.function.local_slots.val + stackWords (values.take count) ≤ U32.max := by
  have max : compiler.height.val ≤ U32.max := by scalar_tac
  rw [observed.height] at max
  by_cases small : count ≤ values.length
  · have mono := stack_words_take_mono values small
    simp only [List.take_length] at mono
    omega
  · simpa [List.take_of_length_le (by omega : values.length ≤ count)] using max

/-- The byte cap leaves room for the largest ordinary callback (three code
and coordinate entries), not merely its first append. -/
theorem SourceCodeBudget.callback_headroom {A} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (aligned : SourceAligned compiler) :
    compiler.function.code.val.length + 3 < 2^32 ∧
    compiler.function.code.val.length + 3 ≤ Usize.max ∧
    compiler.function.source_offsets.val.length + 3 ≤ Usize.max := by
  have words : 2^32 - 1 ≤ Usize.max := by scalar_tac
  unfold SourceCodeBudget SourceAligned at *
  norm_num [Itasca.limits.MAX_MODULE_BYTES] at bounded
  omega

end Itasca.Runtime.Compiler

end
