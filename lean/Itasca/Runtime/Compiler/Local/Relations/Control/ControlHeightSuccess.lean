import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappingLoops
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A normally returning addition determines its mathematical sum, without
assuming the absence of overflow beforehand. -/
theorem control_add_success {ty : UScalarTy} {left right out : UScalar ty}
    (success : (left + right : Result (UScalar ty)) = .ok out) : out.val = left.val + right.val := by
  have spec := UScalar.add_equiv left right
  simp only [success] at spec
  exact spec.2.1

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
