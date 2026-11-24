import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Source.SourceTactics

/-!
Proofs for Runtime / Compiler / Local / Relations / Function.

This module collects EnvironmentContracts, FunctionEnvironment.
Each section documents its contracts and consumers.
-/

/-! ## EnvironmentContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Relations / Function.

This module collects SignatureCapture, EnvironmentContracts.
Each section documents its contracts and consumers.
-/

/-! ## SignatureCapture -/

section

open Itasca.Representation

/-! Exact signature and function parameter-slot capture for scheduler setup. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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

theorem signature_slots_eq (types : List Itasca.wasm_types.ValueType) :
    signatureSlots types = Representation.valueTypeSlots types := by
  have same : Itasca.Translation.valueType = Itasca.Translation.valueType := by
    funext ty
    cases ty <;> rfl
  simp [signatureSlots, Representation.valueTypeSlots, same]

@[step] theorem compiler_type_slots (types : Slice Itasca.wasm_types.ValueType) :
    runtime.compiler.type_slots types ⦃ result =>
      match result with
      | .Ok word => word.val = signatureSlots types.val
      | .Err error => error = .Host ∧ U32.max < signatureSlots types.val ⦄ := by
  unfold runtime.compiler.type_slots
  step with Representation.value_type_slots types as ⟨slots, hs⟩
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
        SignatureMatches signature (ty.params.val.map Itasca.Translation.valueType)
          (ty.results.val.map Itasca.Translation.valueType) ⦄ := by
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
        SignatureMatches signature (type.params.val.map Itasca.Translation.valueType)
          (type.results.val.map Itasca.Translation.valueType) ⦄ := by
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

end Itasca.Compiler

end

/-! ## EnvironmentContracts -/

section

open Itasca.Representation

/-! Scheduler environment capture, exact source metadata and bounded allocation. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation

/-- Independent numerical eligibility of the compiler's environment phase. -/
structure EnvironmentDemand {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (bound : Nat) : Prop where
  functionLimit : env.func_type_indices.length ≤ scheduler.budget.limits.max_functions.val
  typeLimit : env.types.length ≤ scheduler.budget.limits.max_types.val
  signatureWidths : ∀ type ∈ env.types.val,
    signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max
  functionWidths : ∀ type ∈ env.func_types.val, signatureSlots type.params.val ≤ U32.max
  signatureCapacity : scheduler.signatures.length + env.types.length ≤ Usize.max
  signatureReserve : scheduler.signatures.length + env.types.length ≤ bound
  slotCapacity : scheduler.func_param_slots.length + env.func_types.length ≤ Usize.max
  slotReserve : scheduler.func_param_slots.length + env.func_types.length ≤ bound
  functionCapacity : scheduler.functions.length + env.func_type_indices.length ≤ Usize.max
  functionReserve : scheduler.functions.length + env.func_type_indices.length ≤ bound


def SignatureSequence (signatures : List runtime.compiler.Signature)
    (types : List Itasca.wasm_types.FuncType) : Prop :=
  List.Forall₂ (fun signature ty => SignatureMatches signature
    (ty.params.val.map Itasca.Translation.valueType) (ty.results.val.map Itasca.Translation.valueType)) signatures types

theorem SignatureSequence.append {signatures types signature ty}
    (before : SignatureSequence signatures types)
    (last : SignatureMatches signature (ty.params.val.map Itasca.Translation.valueType)
      (ty.results.val.map Itasca.Translation.valueType)) :
    SignatureSequence (signatures ++ [signature]) (types ++ [ty]) := by
  induction before with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

def schedulerFrame {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.completed, scheduler.tail, scheduler.code_start)

abbrev EnvironmentCapture (A : Type) :=
  alloc.vec.Vec runtime.compiler.Signature × alloc.vec.Vec U32 × alloc.vec.Vec Itasca.stream.CodeBatch ×
  alloc.vec.Vec (Option runtime.bytecode.CompiledFunction) × Option Itasca.metadata.Tail × Usize ×
  runtime.compiler.Budget A × core.result.Result Unit Itasca.error.Error

def captureState {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (status : core.result.Result Unit Itasca.error.Error) : EnvironmentCapture A :=
  (scheduler.signatures,scheduler.func_param_slots,scheduler.completed,scheduler.functions,
    scheduler.tail,scheduler.code_start,scheduler.budget,status)

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        have frame : schedulerFrame middle = schedulerFrame before := by
          unfold schedulerFrame
          rw [runtime.compiler.CompileScheduler.capture_signature.inv allocator before middle env index nextResult entry]
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans frame
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, core.result.Result.is_ok] using tail
        have frame : schedulerFrame middle = schedulerFrame before := by
          unfold schedulerFrame
          rw [runtime.compiler.CompileScheduler.capture_func_slots.inv allocator before middle env index nextResult entry]
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans frame
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.types.val.length)
    (prefixMatches : status = .Ok () → SignatureSequence scheduler.signatures.val (env.types.val.take index.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index status ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) =>
      reply = .Ok () → SignatureSequence signatures.val env.types.val ∧
        slots = scheduler.func_param_slots ∧ functions = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun p => env.types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.types.val.length ∧
      (p.2.2 = .Ok () → SignatureSequence p.1.signatures.val (env.types.val.take p.2.1.val) ∧
        p.1.func_param_slots = scheduler.func_param_slots ∧ p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.metadata.Env.impl.types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨currentMatches, sameSlots, sameFunctions⟩ := certified rfl
        have length := List.Forall₂.length_eq currentMatches
        have capacity := env.types.property
        have fits : current.signatures.val.length < Usize.max := by simp [List.length_take, Nat.min_eq_left hi] at length; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with runtime.compiler.CompileScheduler.capture_signature.total ops law current env i env.types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨signature, budget, changedEq, appended, exactSignature⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [hnext, ← List.take_concat_get' env.types.val i.val hb, appended]
          exact currentMatches.append exactSignature
        · rw [changedEq]
          exact sameSlots
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨prefixMatches accepted, rfl, rfl⟩⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_types.val.length)
    (prefixMatches : status = .Ok () → scheduler.func_param_slots.val.map (fun word => word.val) =
      (env.func_types.val.take index.val).map (fun ty => signatureSlots ty.params.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index status ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) =>
      reply = .Ok () →
        signatures = scheduler.signatures ∧ slots.val.map (fun word => word.val) =
          env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        functions = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun p => env.func_types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.func_types.val.length ∧
      (p.2.2 = .Ok () → p.1.signatures = scheduler.signatures ∧
        p.1.func_param_slots.val.map (fun word => word.val) =
          (env.func_types.val.take p.2.1.val).map (fun ty => signatureSlots ty.params.val) ∧
        p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.metadata.Env.impl.func_types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨signaturesEq, currentMatches, sameFunctions⟩ := certified rfl
        have length := congrArg List.length currentMatches
        have capacity := env.func_types.property
        have fits : current.func_param_slots.val.length < Usize.max := by
          simp only [List.length_map, List.length_take, Nat.min_eq_left hi] at length
          omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with runtime.compiler.CompileScheduler.capture_func_slots.total ops law current env i env.func_types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨word, budget, changedEq, appended, exactWidth⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [changedEq]
          exact signaturesEq
        · rw [hnext, ← List.take_concat_get' env.func_types.val i.val hb, appended]
          simp only [List.map_append, List.map_singleton, currentMatches, exactWidth]
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨rfl, prefixMatches accepted, rfl⟩⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status ⦃ (afterFunctions, afterBudget, reply) =>
      reply = .Ok () → afterFunctions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun p => env.func_type_indices.val.length - p.2.2.1.val)
    (fun p => p.2.2.1.val ≤ env.func_type_indices.val.length ∧
      (p.2.2.2 = .Ok () → p.1.val = List.replicate p.2.2.1.val none))
  · rintro ⟨functions, budget, i, result⟩ ⟨hi, filled⟩
    dsimp only at hi filled
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        have initialized := filled rfl
        have capacity := env.func_type_indices.property
        have fits : functions.val.length < Usize.max := by simp [initialized]; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with budget_push ops law budget functions none fits as ⟨status, nextBudget, nextFunctions, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [runtime.compiler.visitor_result.eq, bind_ok]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro _
          rw [appended, initialized, hnext, List.replicate_add]
          simp
        · simp only [runtime.compiler.visitor_result.eq, bind_ok]
          step as ⟨next, hnext⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · rename_i finished
      have same : i.val = env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using filled accepted
  · exact ⟨bound, initialized⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.types.val.length)
    (widths : ∀ type ∈ env.types.val,
      signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length + (env.types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.signatures.length + (env.types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index (.Ok ()) ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) => ∃ after,
        (signatures, slots, completed, functions, tail, codeStart, budget, reply) = captureState after (.Ok ()) ∧
        after = {scheduler with signatures := after.signatures} ∧
        after.signatures.length = scheduler.signatures.length + (env.types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun state => env.types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with signatures := state.1.signatures} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.types.val.length ∧
      state.1.signatures.length + (env.types.val.length-state.2.1.val) =
        scheduler.signatures.length + (env.types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.metadata.Env.impl.types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.types.val[next.val]
      have lookup : env.types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      obtain ⟨params,results⟩ := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with runtime.compiler.CompileScheduler.capture_signature.available ops bound available current env next type lookup params results
        (by omega) (by omega) as ⟨status,middle,accepted,signatures,signature,shape,appended,matched⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.types.val.length := by
        have ended : env.types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_types.val.length)
    (widths : ∀ type ∈ env.func_types.val,
      signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index (.Ok ()) ⦃ (signatures, slots, completed, functions, tail, codeStart, budget, reply) => ∃ after,
        (signatures, slots, completed, functions, tail, codeStart, budget, reply) = captureState after (.Ok ()) ∧
        after = {scheduler with func_param_slots := after.func_param_slots} ∧
        after.func_param_slots.length = scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun state => env.func_types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with func_param_slots := state.1.func_param_slots} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.func_types.val.length ∧
      state.1.func_param_slots.length + (env.func_types.val.length-state.2.1.val) =
        scheduler.func_param_slots.length + (env.func_types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.metadata.Env.impl.func_types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.func_types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.func_types.val[next.val]
      have lookup : env.func_types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      have params := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with runtime.compiler.CompileScheduler.capture_func_slots.available ops bound available current env next type lookup params
        (by omega) (by omega) as ⟨status,middle,accepted,slots,amount,shape,appended,counted⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.func_types.val.length := by
        have ended : env.func_types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A) (env : Itasca.metadata.Env) (index : Usize)
    (inside : index.val ≤ env.func_type_indices.val.length)
    (capacity : functions.length + (env.func_type_indices.val.length-index.val) ≤ Usize.max)
    (request : functions.length + (env.func_type_indices.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index (.Ok ()) ⦃ (afterFunctions, afterBudget, reply) =>
        reply = .Ok () ∧ afterBudget = budget ∧
        afterFunctions.length = functions.length + (env.func_type_indices.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun state => env.func_type_indices.val.length-state.2.2.1.val)
    (fun state => state.2.1 = budget ∧ state.2.2.2 = .Ok () ∧
      state.2.2.1.val ≤ env.func_type_indices.val.length ∧
      state.1.length + (env.func_type_indices.val.length-state.2.2.1.val) =
        functions.length + (env.func_type_indices.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst charged status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.metadata.Env.impl.func_type_indices,bind_ok]
    split
    · rename_i more
      have inbounds : next.val < env.func_type_indices.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with budget_push_available ops bound available budget current none (by change current.length < Usize.max; omega)
        (by change current.length + 1 ≤ bound; omega)
        as ⟨status,charged,after,accepted,same,appended⟩
      subst status charged
      simp only [runtime.compiler.visitor_result.eq,bind_ok]
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = env.func_type_indices.val.length := by
        have ended : env.func_type_indices.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,rfl,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.inv {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.Config)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready at accepted
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok] at accepted
  split at accepted
  · simp [runtime.compiler.Budget.reject.eq] at accepted
  · simp only [Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · simp [runtime.compiler.Budget.reject.eq] at accepted
    · obtain ⟨⟨signatures, slots, completed, functions, tail, start, budget, status⟩, loop0, rest⟩ :=
        bind_ok_inv _ _ _ accepted
      have frame0 := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.inv allocator before env 0#usize (.Ok ()) _ loop0
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨signatures1, slots1, completed1, functions1, tail1, start1, budget1, status1⟩, loop1, rest⟩ :=
          bind_ok_inv _ _ _ rest
        have frame1 := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.inv allocator
          ⟨signatures, slots, completed, functions, tail, start, budget⟩ env 0#usize (.Ok ()) _ loop1
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨functions2, budget2, status2⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unit =>
            cases unit
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              Result.ok.injEq, Prod.mk.injEq] at rest
            obtain ⟨_, output⟩ := rest
            subst after
            exact frame1.trans frame0

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (emptyTypes : scheduler.signatures.val = [])
    (emptySlots : scheduler.func_param_slots.val = []) (emptyFunctions : scheduler.functions.val = []) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ (reply, after) =>
      ∀ config, reply = .Ok config →
        SignatureSequence after.signatures.val env.types.val ∧
        after.func_param_slots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        after.functions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
  split
  · simp [runtime.compiler.Budget.reject.eq]
  · simp only [Itasca.metadata.Env.impl.types, bind_ok]
    split
    · simp [runtime.compiler.Budget.reject.eq]
    · step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total ops law scheduler env 0#usize (.Ok ())
        (by simp) (by intro _; simp [emptyTypes, SignatureSequence])
        as ⟨signatures, words, completed, functions, tail, codeStart, budget, status, effect⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        obtain ⟨sequence, slotsSame, functionsSame⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
        step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.total ops law
          ⟨signatures, words, completed, functions, tail, codeStart, budget⟩ env 0#usize (.Ok ())
          (by simp) (by intro _; simp [slotsSame, emptySlots])
          as ⟨signatures1, words1, completed1, functions1, tail1, codeStart1, budget1, status1, effect1⟩
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨sameSignatures, slotsExact, functionsSame1⟩ := effect1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total ops law budget1 functions1 env 0#usize (.Ok ())
            (by simp) (by intro _; simp [functionsSame1, functionsSame, emptyFunctions])
            as ⟨functions2, budget2, status2, effect2⟩
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro config accepted
            refine ⟨?_, slotsExact, effect2 rfl⟩
            simpa only [sameSignatures] using sequence

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ (reply, after) => reply = .Ok ⟨25000#usize,4#usize⟩ ∧ after.budget = scheduler.budget ⦄ := by
  have functions : ¬ Slice.len (alloc.vec.Vec.deref env.func_type_indices) > scheduler.budget.limits.max_functions := by
    have limit := demand.functionLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  have types : ¬ Slice.len (alloc.vec.Vec.deref env.types) > scheduler.budget.limits.max_types := by
    have limit := demand.typeLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.metadata.Env.impl.func_type_indices,Itasca.metadata.Env.impl.types,bind_ok,if_neg functions,if_neg types]
  obtain ⟨captured,actual,first,same,firstShape,firstLength⟩ := WP.spec_imp_exists
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.available ops bound available scheduler env 0#usize (by simp)
      demand.signatureWidths (by simpa using demand.signatureCapacity) (by simpa using demand.signatureReserve))
  rcases captured with ⟨firstOutputSignatures, firstOutputSlots, firstOutputCompleted, firstOutputFunctions, firstOutputTail, firstOutputStart, firstOutputBudget, firstOutputStatus⟩
  dsimp only at same
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have slots : first.func_param_slots = scheduler.func_param_slots :=
    congrArg (fun value => value.func_param_slots) firstShape
  have firstFunctions : first.functions = scheduler.functions := congrArg (fun value => value.functions) firstShape
  have firstBudget : first.budget = scheduler.budget := congrArg (fun value => value.budget) firstShape
  obtain ⟨captured,actual,second,same,secondShape,secondLength⟩ := WP.spec_imp_exists
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.available ops bound available first env 0#usize (by simp)
      demand.functionWidths (by simpa [slots] using demand.slotCapacity) (by simpa [slots] using demand.slotReserve))
  rcases captured with ⟨secondOutputSignatures, secondOutputSlots, secondOutputCompleted, secondOutputFunctions, secondOutputTail, secondOutputStart, secondOutputBudget, secondOutputStatus⟩
  dsimp only at same
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have secondFunctions : second.functions = scheduler.functions :=
    (congrArg (fun value => value.functions) secondShape).trans firstFunctions
  have secondBudget : second.budget = scheduler.budget :=
    (congrArg (fun value => value.budget) secondShape).trans firstBudget
  step with runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.available ops bound available second.functions second.budget env 0#usize
    (by simp) (by simpa [secondFunctions] using demand.functionCapacity)
    (by simpa [secondFunctions] using demand.functionReserve)
    as ⟨functions,budget,status,accepted,sameBudget,length⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
  exact ⟨rfl,by rw [sameBudget,secondBudget]⟩

/-- The function-vector loop's accepted result is the exact replicated source
length established by its total contract. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.inv
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none)
    {output} (called : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status = .ok output) :
    let (afterFunctions, _, reply) := output
    reply = .Ok () → afterFunctions.val = List.replicate env.func_type_indices.val.length none := by
  have effect := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total
    ops law budget functions env index status bound initialized
  rw [called, WP.spec_ok] at effect
  exact effect

end Itasca.Compiler

end

end

/-! ## FunctionEnvironment -/

section

open Itasca.Representation

/-! ## Signatures -/

section

/-! Compiler signature capture: total exact word counting, retained source
value/word arities, and source block-signature resolution. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std

def SignatureTable (signatures : Slice runtime.compiler.Signature) (types : List functype) : Prop :=
  ∀ (i : Nat) (signature : runtime.compiler.Signature), signatures.val[i]? = some signature →
    ∃ params results : List valtype, types[i]? = some (.mk_functype (.mk_list params) (.mk_list results)) ∧
      SignatureMatches signature params results

/-- Capturing an accepted module type appends its exact value and word counts.
The slot accumulator is total, and rejects only a width above the u32 bound. -/
@[step] theorem capture_signature {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (ty : Itasca.wasm_types.FuncType)
    (lookup : env.types.val[index.val]? = some ty)
    (fits : scheduler.signatures.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ out =>
      out.1 = .Ok () → ∃ signature budget,
        out.2 = { scheduler with signatures := out.2.signatures, budget } ∧
        out.2.signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (ty.params.val.map Itasca.Translation.valueType)
          (ty.results.val.map Itasca.Translation.valueType) ⦄ := by
  exact runtime.compiler.CompileScheduler.capture_signature.total ops law scheduler env index ty lookup fits

end Itasca.Compiler

end

/-! ## FunctionEntry -/

section

/-!
The successful function-start callback establishes the zero-operand layout, source coordinates, and the root control frame used by all later callbacks.

Main declarations: `compiler_function_start` and `compiler_new`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The successful function-start callback establishes the zero-operand layout,
source coordinates, and the root control frame used by all later callbacks. -/
@[step] theorem compiler_function_start {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val + bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val + bodyEnd.val ≤ Usize.max)
    (emptyLocals : compiler.function.locals.val = [])
    (localLayout : LocalLayout compiler)
    (emptyOperands : compiler.before.val = [])
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
      out.1 = .Ok () → CompilerLayout out.2 [] ∧
        out.2.reachable = compiler.reachable ∧
        out.2.function.slot_count = out.2.function.local_slots ∧
        out.2.function.locals.val = ctx.locals.val ∧
        out.2.function.param_slots = signature.param_slots ∧
        out.2.function.type_index = typeIndex ∧
        out.2.function.body_start.val = compiler.batch_start.val + bodyBegin.val ∧
        out.2.function.body_end.val = compiler.batch_start.val + bodyEnd.val ∧
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = compiler.frames.val ++
          [⟨0#usize, .Body, out.2.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        out.2.function.controls.val = compiler.function.controls.val ++
          [⟨.Body, out.2.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize,
            0#usize, signature.results⟩] ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.total
    ops law compiler ctx typeIndex signature bodyBegin bodyEnd
    ⟨lookup, beginFits, endFits, emptyLocals, localLayout, emptyOperands, mapsFit, framesFit⟩

@[step] theorem compiler_new {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      LocalLayout out ∧ out.function.locals.val = [] ∧ out.before.val = [] ∧
        out.function.controls.val = [] ∧ out.frames.val = [] ∧
        out.function.code.val = [] ∧ out.reachable = true ∧
        out.signatures = signatures ∧ out.func_param_slots = functionSlots ∧
        out.batch_start = batchStart ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.new.eq, WP.spec_ok]
  constructor
  · constructor <;> simp [compilerLocals, alloc.vec.Vec.new, slots]
  · simp [alloc.vec.Vec.new]
end Itasca.Compiler

end

/-! ## FunctionEnvironment -/

section

/-!
Function entry and local declarations preserve the scheduler signature tables and batch origin.

Main declarations: `FunctionEnvironment`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve the scheduler signature tables and batch origin. -/
def FunctionEnvironment {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.signatures, after.func_param_slots, after.batch_start) =
    (before.signatures, before.func_param_slots, before.batch_start)

theorem FunctionEnvironment.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : FunctionEnvironment before middle) (second : FunctionEnvironment middle after) :
    FunctionEnvironment before after := Eq.trans second first

theorem compiler_function_start_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    FunctionEnvironment before after := by
  have frame := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.inv
    ops before after ctx typeIndex start finish status accepted
  unfold FunctionEnvironment
  rw [frame]

end Itasca.Compiler

end

end
