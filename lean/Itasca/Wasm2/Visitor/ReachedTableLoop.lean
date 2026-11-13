import Itasca.Wasm2.Visitor.BrTable
namespace Itasca.Wasm2.Visitor
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The real Wasm 2 target loop terminates from a reached-state body contract.
The count/index measure includes the final default-target iteration. -/
theorem _root_.Itasca.code.branch_table_with_loop.total_on {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : metadata.Env)
     (count : U32)
    (inv : code.BodyState → V → Option Usize → U32 → Prop)
    (post : code.BodyState → V → Prop)
    (steps : ∀ st v arity index, index.val ≤ count.val → inv st v arity index →
      tableBody visitor data env count st v arity index ⦃ result =>
        match result with
        | .done out => out.1 = .Ok () → post out.2.1 out.2.2
        | .cont next => next.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.val ∧
            inv ⟨next.1⟩ next.2.1 next.2.2.1 next.2.2.2 ⦄)
    (st : code.BodyState) (v : V) (arity : Option Usize) (index : U32) (bound : index.val ≤ count.val) (initial : inv st v arity index) :
    code.branch_table_with_loop visitor st.core data env v count arity index ⦃ result =>
      result.1 = .Ok () → post result.2.1 result.2.2 ⦄ := by
  unfold code.branch_table_with_loop
  apply loop.spec_decr_nat (fun state => count.val-state.2.2.2.val)
    (fun state => state.2.2.2.val ≤ count.val ∧
      inv ⟨state.1⟩ state.2.1 state.2.2.1 state.2.2.2)
  · rintro ⟨core,value,current,index⟩ ⟨bound,held⟩
    dsimp only
    rw [tableBody_eq visitor data env count ⟨core⟩ value current index]
    apply WP.spec_mono (steps ⟨core⟩ value current index bound held)
    intro result resultPost
    cases result with
    | done output => exact resultPost
    | cont next =>
      exact ⟨⟨resultPost.1,resultPost.2.2⟩,by omega⟩
  · exact ⟨bound,initial⟩
end Itasca.Wasm2.Visitor
