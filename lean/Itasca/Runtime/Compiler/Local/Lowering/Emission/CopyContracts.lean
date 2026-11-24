import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions

/-!
Proofs for Runtime / Compiler / Local / Lowering / Emission.

This module collects Pair, Copy.
Each section documents its contracts and consumers.
-/

/-! ## Pair -/

section

/-! Pair-table insertion: law-free frame, exact allocation effect, and availability. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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

end Itasca.Compiler

end

/-! ## Copy -/

section

/-!
Copy contracts distinguish elided transfers from emitted width-specific
instructions. Inversion exposes the actual result; totality and availability
state their capacity and allocation premises. Successful nonempty, nonidentity
transfers produce the expected emission certificate.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Exact control flow of a transfer: empty and identity copies are elided. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.copy.eq {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) :
    runtime.compiler.FunctionCompiler.copy ops before dst src count =
      if count = 0#u32 ∨ src = dst then .ok (.Ok (), before)
      else runtime.compiler.FunctionCompiler.emit ops before (transferInstruction dst src count) := by
  unfold runtime.compiler.FunctionCompiler.copy
  by_cases zero : count = 0#u32
  · rw [if_pos zero, if_pos (Or.inl zero)]
  · rw [if_neg zero]
    by_cases same : src = dst
    · rw [if_pos same, if_pos (Or.inr same)]
    · rw [if_neg same, if_neg (fun choice => choice.elim zero same)]
      split
      next =>
        simp only [bind_ok]
        rfl
      next =>
        simp only [bind_ok]
        rfl
      next notOne notTwo =>
        have one : count.val ≠ 1 := by
          intro equal
          exact notOne (UScalar.eq_of_val_eq equal)
        have two : count.val ≠ 2 := by
          intro equal
          exact notTwo (UScalar.eq_of_val_eq equal)
        simp only [bind_ok, transferInstruction, if_neg one, if_neg two]

/-- The observable alternatives of a normal copy return. The emitted alternative
retains its actual call, so allocator-independent facets require no extra law. -/
def CopyEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ((count = 0#u32 ∨ src = dst) ∧ status = .Ok () ∧ after = before) ∨
    (count ≠ 0#u32 ∧ src ≠ dst ∧
      runtime.compiler.FunctionCompiler.emit ops before (transferInstruction dst src count) = .ok (status, after))

/-- Inversion distinguishes elision from the single width-selected emission. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.copy.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    CopyEffect ops before after dst src count status := by
  rw [runtime.compiler.FunctionCompiler.copy.eq] at called
  by_cases elided : count = 0#u32 ∨ src = dst
  · rw [if_pos elided] at called
    have result := Result.ok_injective called
    exact Or.inl ⟨elided, (congrArg Prod.fst result).symm, (congrArg Prod.snd result).symm⟩
  · rw [if_neg elided] at called
    exact Or.inr ⟨fun zero => elided (Or.inl zero), fun same => elided (Or.inr same), called⟩

/-- Copy preserves the same allocator-independent frame as emission. -/
theorem CopyEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {dst src count : U32}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : CopyEffect ops before after dst src count status) : EmitFrame before after := by
  rcases effect with ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · subst after
    rfl
  · exact (runtime.compiler.FunctionCompiler.emit.inv ops before after _ status emitted).1

/-- Under allocator correctness, success either leaves the compiler unchanged or
has the exact single-instruction effect. -/
theorem CopyEffect.exact {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {dst src count : U32}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : CopyEffect ops before after dst src count status) (law : Platform.AllocCorrect ops)
    (accepted : status = .Ok ()) :
    after = before ∨ EmittedExact before after (transferInstruction dst src count) := by
  rcases effect with ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · exact Or.inl same
  · exact Or.inr (((runtime.compiler.FunctionCompiler.emit.inv ops before after _ status emitted).2 law).2 accepted)

/-- Correct allocation and representable append lengths and coordinates make
copy return normally, including ordinary Rust errors. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.copy.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.copy ops before dst src count ⦃ _ => True ⦄ := by
  rw [runtime.compiler.FunctionCompiler.copy.eq]
  split
  · exact WP.spec.ret True.intro
  · exact runtime.compiler.FunctionCompiler.emit.total ops law before _ codeFits sourceFits coordinateFits

/-- Independent room for the one instruction a nonelided copy emits. -/
structure CopyDemand {A : Type} (before : runtime.compiler.FunctionCompiler A) (bound : Nat) : Prop where
  pc : before.function.code.length ≤ U32.max
  codeCapacity : before.function.code.length < Usize.max
  sourceCapacity : before.function.source_offsets.length < Usize.max
  codeReserve : before.function.code.length + 1 ≤ bound
  sourceReserve : before.function.source_offsets.length + 1 ≤ bound
  coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max
  instruction : before.budget.instructions.val < before.budget.limits.max_instructions.val

/-- Available allocation guarantees exact successful emission when needed;
elided transfers need no resource room. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.copy.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (demand : count ≠ 0#u32 → src ≠ dst → CopyDemand before bound) :
    runtime.compiler.FunctionCompiler.copy ops before dst src count ⦃ (status, after) =>
      status = .Ok () ∧ (if count = 0#u32 ∨ src = dst then after = before
        else EmittedExact before after (transferInstruction dst src count)) ⦄ := by
  rw [runtime.compiler.FunctionCompiler.copy.eq]
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [if_pos elided]
    exact WP.spec.ret ⟨rfl, rfl⟩
  · simp only [if_neg elided]
    have room := demand (fun zero => elided (Or.inl zero)) (fun same => elided (Or.inr same))
    exact runtime.compiler.FunctionCompiler.emit.available ops bound available before _
      room.pc room.codeCapacity room.sourceCapacity room.codeReserve room.sourceReserve room.coordinate room.instruction

/-- Every nonempty, nonidentity transfer emits the width-selected instruction. -/
@[step] theorem compiler_copy {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (nonempty : count ≠ 0#u32) (different : src ≠ dst)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ out =>
      out.1 = .Ok () → Emitted compiler out.2 (transferInstruction dst src count) ⦄ := by
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.copy.total ops law compiler dst src count codeFits sourceFits coordinateFits)
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  rcases runtime.compiler.FunctionCompiler.copy.inv ops compiler after dst src count status called with
    ⟨elided, _, _⟩ | ⟨_, _, emitted⟩
  · exact False.elim (elided.elim nonempty different)
  · exact (((runtime.compiler.FunctionCompiler.emit.inv ops compiler after _ status emitted).2 law).2 accepted).emitted
end Itasca.Compiler

end
