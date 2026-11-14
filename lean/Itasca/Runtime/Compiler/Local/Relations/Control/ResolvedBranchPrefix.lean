import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Relations.Emission.EmissionSources
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix

/-!
Sections, each formerly its own module: ControlHeightSuccess, BranchSuccessEmit, ResolvedBranchPrefix.
-/

/-! ## ControlHeightSuccess -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful height computation certifies its exact sum. This partial
correctness statement also covers dormant source stacks; it makes no totality
claim for operands whose mathematical slot count exceeds u32. -/
theorem control_stack_height_success (values : Slice Itasca.code.StackType)
    (count : Usize) (initial out : U32) (countFits : count.val ≤ values.val.length)
    (success : runtime.compiler.control.stack_height values count initial = .ok out) :
    out.val = initial.val + stackWords (values.val.take count.val) := by
  let inv : U32 × Usize → Prop := fun state =>
    state.2.val ≤ count.val ∧ state.1.val = initial.val + stackWords (values.val.take state.2.val)
  have body : ∀ state, inv state → ∀ flow,
      runtime.compiler.control.stack_height_loop.body values count state.1 state.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ count.val - next.2.val < count.val - state.2.val
      | .done result => result.val = initial.val + stackWords (values.val.take count.val) := by
    rintro ⟨height, index⟩ ⟨bound, exactHeight⟩ flow call
    dsimp only at bound exactHeight
    unfold runtime.compiler.control.stack_height_loop.body at call
    split at call
    · rename_i more
      have ltCount : index.val < count.val := more
      have inBounds : index.val < values.val.length := by omega
      obtain ⟨value, read, rest⟩ := initializer_bind_success call
      have readSpec : Slice.index_usize values index ⦃ found => found = values.val[index.val] ⦄ := by
        step as ⟨found, atFound⟩
        exact atFound
      rw [read, WP.spec_ok] at readSpec
      subst value
      obtain ⟨word, widthCall, rest⟩ := initializer_bind_success rest
      have widthSpec := control_stack_width values.val[index.val]
      rw [widthCall, WP.spec_ok] at widthSpec
      obtain ⟨nextHeight, added, rest⟩ := initializer_bind_success rest
      obtain ⟨nextIndex, advanced, rest⟩ := initializer_bind_success rest
      have returned := Result.ok_injective rest
      subst flow
      have heightEq := control_add_success added
      have indexEq := control_add_success advanced
      have increment := stack_words_take_succ values.val index.val inBounds
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp only; scalar_tac
      · dsimp only
        rw [heightEq, exactHeight, widthSpec]
        have next : nextIndex.val = index.val + 1 := by simpa using indexEq
        rw [next, increment]
        omega
      · dsimp only; scalar_tac
    · rename_i done
      have same : index.val = count.val := by scalar_tac
      have returned := Result.ok_injective call
      subst flow
      simpa only [same] using exactHeight
  exact initializer_loop_success
    (fun state => runtime.compiler.control.stack_height_loop.body values count state.1 state.2)
    (fun state => count.val - state.2.val) inv
    (fun result : U32 => result.val = initial.val + stackWords (values.val.take count.val))
    (by
      intro state hi flow call
      have h := body state hi flow call
      cases flow <;> exact h) (initial, 0#usize) (by simp [inv, stackWords]) out success

end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessEmit -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
/-- Exact successful emission needs no separate vector-capacity or coordinate premise. -/
theorem compiler_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    Emitted before after instruction := by
  exact (((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction (.Ok ()) accepted).2 law).2 rfl).emitted

theorem compiler_copy_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (nonempty : count ≠ 0#u32) (different : src ≠ dst)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    Emitted before after (transferInstruction dst src count) := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  rw [if_neg nonempty, if_neg different] at accepted
  split at accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy dst src) accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy2 dst src) accepted
  · rename_i notOne notTwo
    simp only [bind_ok] at accepted
    have h1 : count.val ≠ 1 := by intro eq; apply notOne; apply UScalar.eq_of_val_eq; exact eq
    have h2 : count.val ≠ 2 := by intro eq; apply notTwo; apply UScalar.eq_of_val_eq; exact eq
    simpa [transferInstruction, h1, h2] using compiler_emit_success ops law before after (.CopyN dst src count) accepted
end Itasca.Runtime.Compiler

end

/-! ## ResolvedBranchPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Retargeting a newly emitted BR in its selected open group preserves the
previous resolved prefix and appends the final literal branch sequence. -/
theorem resolved_code_new_br (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchInstructions dst src count old)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchInstructions dst src count group.target := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchInstructions, elided, BranchKind.instruction] using
      resolved_code_new_branch code [] before after group .jump old site (by simpa [elided] using position) inside
  · simpa [branchInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolved_code_new_branch code [transferInstruction dst src count] before after group .jump old site
        (by simpa [elided] using position) inside

end Itasca.Runtime.Compiler

end
