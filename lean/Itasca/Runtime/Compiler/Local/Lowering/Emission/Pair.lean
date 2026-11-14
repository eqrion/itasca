import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs

/-! Pair-table insertion: law-free frame, exact allocation effect, and availability. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Pair insertion only changes the budget and indirect-call table. -/
def PairFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with budget := after.budget, function := {before.function with indirect := after.function.indirect}}

/-- Successful insertion retains the budget and returns the appended pair index. -/
def PairedExact {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (a b entry : U32) : Prop :=
  ∃ pairs, after = {before with function := {before.function with indirect := pairs}} ∧
    pairs.val = before.function.indirect.val ++ [(a,b)] ∧
    entry.val = before.function.indirect.val.length

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.pair.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (a b : U32) (status : core.result.Result U32 Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    PairFrame before after ∧ (Platform.AllocCorrect ops →
      (after.function.indirect.val = before.function.indirect.val ∨
        after.function.indirect.val = before.function.indirect.val ++ [(a,b)]) ∧
      (∀ entry, status = .Ok entry → PairedExact before after a b entry)) := by
  unfold runtime.compiler.FunctionCompiler.pair at called
  obtain ⟨indexResult, indexCall, rest⟩ := bind_ok_inv _ _ _ called
  cases indexResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    refine ⟨rfl, fun _ => ⟨Or.inl rfl, ?_⟩⟩
    intro entry impossible
    cases impossible
  | Ok index =>
    have indexSpec := bounded_index (alloc.vec.Vec.len before.function.indirect)
    rw [indexCall, WP.spec_ok] at indexSpec
    have indexEq := indexSpec index rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨pushed, budget, pairs⟩, pushCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases pushed with
    | Err error =>
      simp only [uncurry_apply_pair,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      refine ⟨rfl, fun law => ⟨?_, ?_⟩⟩
      · exact budget_push_code_result ops law before.budget budget before.function.indirect pairs (a,b) (.Err error) pushCall
      · intro entry impossible
        cases impossible
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,
        bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      refine ⟨rfl, fun law => ?_⟩
      obtain ⟨sameBudget, appended⟩ := budget_push_success ops law before.budget budget before.function.indirect pairs (a,b) pushCall
      refine ⟨Or.inr appended, ?_⟩
      intro entry same
      cases same
      exact ⟨pairs, by rw [sameBudget], appended, indexEq⟩

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.pair.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (a b : U32)
    (fits : before.function.indirect.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.pair ops before a b ⦃ out => PairFrame before out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pair
  step with bounded_index (alloc.vec.Vec.len before.function.indirect) as ⟨indexResult, _⟩
  cases indexResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    rfl
  | Ok index =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law before.budget before.function.indirect (a,b) fits
      as ⟨answer, budget, pairs, effect⟩
    cases answer <;> simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok] <;> rfl

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.pair.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (a b : U32)
    (indexBound : before.function.indirect.length ≤ U32.max)
    (capacity : before.function.indirect.length < Usize.max)
    (request : before.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.pair ops before a b ⦃ out =>
      ∃ entry, out.1 = .Ok entry ∧ PairedExact before out.2 a b entry ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pair
  step with bounded_index_available (alloc.vec.Vec.len before.function.indirect) indexBound
    as ⟨status, index, accepted, indexEq⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available before.budget before.function.indirect
    (a,b) capacity request as ⟨status, budget, pairs, accepted, same, appended⟩
  rw [accepted]
  simp only [bind_ok]
  exact ⟨index, rfl, pairs, by rw [same], appended, indexEq⟩

end Itasca.Runtime.Compiler
