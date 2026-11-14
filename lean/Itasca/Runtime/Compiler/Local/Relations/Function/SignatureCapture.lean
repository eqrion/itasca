import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations

/-! Exact signature and function parameter-slot capture for scheduler setup. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Signature capture retains the complete scheduler outside its signature
vector and budget, for every normal status and arbitrary allocator. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_signature.inv
    {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (status : core.result.Result Unit Itasca.error.Error)
    (called : runtime.compiler.CompileScheduler.capture_signature ops before env index = .ok (status, after)) :
    after = {before with signatures := after.signatures, budget := after.budget} := by
  unfold runtime.compiler.CompileScheduler.capture_signature at called
  obtain ⟨types, _, rest⟩ := bind_ok_inv _ _ _ called
  obtain ⟨signature, _, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨params, _, rest⟩ := bind_ok_inv _ _ _ rest
  cases params with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, rfl⟩ := rest
    rfl
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨results, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases results with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      rfl
    | Ok results =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, budget, signatures⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨_, _, rest⟩ := bind_ok_inv _ _ _ rest
      have same := congrArg Prod.snd (Result.ok_injective rest)
      dsimp only at same
      subst after
      rfl

/-- Parameter-slot capture retains every scheduler component other than its
slot vector and budget, independently of allocator behavior. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_func_slots.inv
    {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (status : core.result.Result Unit Itasca.error.Error)
    (called : runtime.compiler.CompileScheduler.capture_func_slots ops before env index = .ok (status, after)) :
    after = {before with func_param_slots := after.func_param_slots, budget := after.budget} := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots at called
  obtain ⟨types, _, rest⟩ := bind_ok_inv _ _ _ called
  obtain ⟨signature, _, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨params, _, rest⟩ := bind_ok_inv _ _ _ rest
  cases params with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, rfl⟩ := rest
    rfl
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, slots⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨_, _, rest⟩ := bind_ok_inv _ _ _ rest
    have same := congrArg Prod.snd (Result.ok_injective rest)
    dsimp only at same
    subst after
    rfl

def signatureSlots (types : List Itasca.wasm_types.ValueType) : Nat :=
  slots (types.map Itasca.Translate.valueType)

theorem signature_slots_eq (types : List Itasca.wasm_types.ValueType) :
    signatureSlots types = Interp.valueTypeSlots types := by
  have same : Itasca.Translate.valueType = Interp.sourceType := by
    funext ty
    cases ty <;> rfl
  simp [signatureSlots, Interp.valueTypeSlots, same]

@[step] theorem compiler_type_slots (types : Slice Itasca.wasm_types.ValueType) :
    runtime.compiler.type_slots types ⦃ result =>
      match result with
      | .Ok word => word.val = signatureSlots types.val
      | .Err error => error = .Host ∧ U32.max < signatureSlots types.val ⦄ := by
  unfold runtime.compiler.type_slots
  step with Interp.value_type_slots types as ⟨slots, hs⟩
  rw [← signature_slots_eq] at hs
  have maxCast : (UScalar.cast .Usize core.num.U32.MAX).val = U32.max := by
    simp [core.num.U32.MAX, U32.rMax, U32.max, U32.numBits]
  cases slots with
  | none =>
    simp only at hs
    simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    scalar_tac
  | some total =>
    simp only at hs
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, by scalar_tac⟩
    · simp only [WP.spec_ok]
      rw [UScalar.cast_val_eq]
      scalar_tac

structure SignatureMatches (signature : runtime.compiler.Signature)
    (params results : List valtype) : Prop where
  parameters : signature.params.val = params.length
  resultArity : signature.results.val = results.length
  paramWords : signature.param_slots.val = slots params
  resultWords : signature.result_slots.val = slots results

/-- Independent source signature width excludes the actual accumulator error. -/
theorem type_slots_available (types : Slice Itasca.wasm_types.ValueType)
    (bounded : signatureSlots types.val ≤ U32.max) :
    runtime.compiler.type_slots types ⦃ out =>
      ∃ amount, out = .Ok amount ∧ amount.val = signatureSlots types.val ⦄ := by
  apply WP.spec_mono (compiler_type_slots types)
  intro out counted
  cases out with
  | Ok amount => exact ⟨amount,rfl,counted⟩
  | Err error => omega

theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_signature.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (ty : Itasca.wasm_types.FuncType)
    (lookup : env.types.val[index.val]? = some ty)
    (fits : scheduler.signatures.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ (status, after) =>
      status = .Ok () → ∃ signature budget,
        after = { scheduler with signatures := after.signatures, budget } ∧
        after.signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (ty.params.val.map Itasca.Translate.valueType)
          (ty.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.metadata.Env.impl.types, bind_ok]
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index.val < env.types.deref.length := by simpa [alloc.vec.Vec.deref] using bound
  step as ⟨actual, hactual⟩
  have same : actual = ty := by
    simpa [List.getElem?_eq_getElem bound, alloc.vec.Vec.deref, hactual] using lookup
  rw [same]
  step with compiler_type_slots ty.params.deref as ⟨params, hparams⟩
  cases params with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok paramWords =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_type_slots ty.results.deref as ⟨results, hresults⟩
    cases results with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok resultWords =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law scheduler.budget scheduler.signatures
        ⟨alloc.vec.Vec.len ty.params, alloc.vec.Vec.len ty.results, paramWords, resultWords⟩ fits
        as ⟨status, budget, signatures, pushed⟩
      rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [runtime.compiler.visitor_result.eq, bind_ok, WP.spec_ok]
        intro accepted
        refine ⟨_, scheduler.budget, rfl, appended, ?_⟩
        constructor
        · simp [alloc.vec.Vec.len]
        · simp [alloc.vec.Vec.len]
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hparams
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hresults
      · simp [runtime.compiler.visitor_result.eq]

theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_func_slots.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (ty : Itasca.wasm_types.FuncType)
    (lookup : env.func_types.val[index.val]? = some ty)
    (fits : scheduler.func_param_slots.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ (status, after) =>
      status = .Ok () → ∃ word budget,
        after = { scheduler with func_param_slots := after.func_param_slots, budget } ∧
        after.func_param_slots.val = scheduler.func_param_slots.val ++ [word] ∧
        word.val = signatureSlots ty.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.metadata.Env.impl.func_types, bind_ok]
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index.val < env.func_types.deref.length := by simpa [alloc.vec.Vec.deref] using bound
  step as ⟨actual, hactual⟩
  have same : actual = ty := by
    simpa [List.getElem?_eq_getElem bound, alloc.vec.Vec.deref, hactual] using lookup
  rw [same]
  step with compiler_type_slots ty.params.deref as ⟨params, hparams⟩
  cases params with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok paramWords =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law scheduler.budget scheduler.func_param_slots paramWords fits
      as ⟨status, budget, words, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [runtime.compiler.visitor_result.eq, bind_ok, WP.spec_ok]
      intro accepted
      refine ⟨paramWords, scheduler.budget, rfl, appended, ?_⟩
      simpa [alloc.vec.Vec.deref] using hparams
    · simp [runtime.compiler.visitor_result.eq]


theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_signature.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (type : Itasca.wasm_types.FuncType) (lookup : env.types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (results : signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length < Usize.max)
    (request : scheduler.signatures.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ (status, after) =>
      status = .Ok () ∧ ∃ signatures signature,
        after = {scheduler with signatures} ∧
        signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (type.params.val.map Itasca.Translate.valueType)
          (type.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.metadata.Env.impl.types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,params,accepted,paramWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with type_slots_available type.results.deref (by simpa [alloc.vec.Vec.deref] using results) as ⟨status,returned,accepted,resultWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.signatures
    ⟨alloc.vec.Vec.len type.params,alloc.vec.Vec.len type.results,params,returned⟩ capacity request
    as ⟨status,budget,signatures,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result.eq,bind_ok,WP.spec_ok]
  refine ⟨rfl,signatures,_,?_,appended,?_⟩
  · rw [sameBudget]
  · constructor
    · simp [alloc.vec.Vec.len]
    · simp [alloc.vec.Vec.len]
    · simpa [signatureSlots,alloc.vec.Vec.deref] using paramWords
    · simpa [signatureSlots,alloc.vec.Vec.deref] using resultWords


theorem _root_.Itasca.runtime.compiler.CompileScheduler.capture_func_slots.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (type : Itasca.wasm_types.FuncType) (lookup : env.func_types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length < Usize.max)
    (request : scheduler.func_param_slots.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ (status, after) =>
      status = .Ok () ∧ ∃ slots amount,
        after = {scheduler with func_param_slots := slots} ∧
        slots.val = scheduler.func_param_slots.val ++ [amount] ∧
        amount.val = signatureSlots type.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.metadata.Env.impl.func_types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,amount,accepted,counted⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.func_param_slots amount capacity request
    as ⟨status,budget,slots,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result.eq,bind_ok,WP.spec_ok]
  exact ⟨rfl,slots,amount,by rw [sameBudget],appended,by simpa [alloc.vec.Vec.deref] using counted⟩


end Itasca.Runtime.Compiler
