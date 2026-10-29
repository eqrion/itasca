import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterBlock
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Support.ControlTranslation
import Itasca.Runtime.Representation.Values
/-! Compiler signature capture: total exact word counting, retained source
value/word arities, and source block-signature resolution. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def signatureSlots (types : List Itasca.types.ValueType) : Nat :=
  slots (types.map Itasca.Translate.valueType)

theorem signatureSlots_eq (types : List Itasca.types.ValueType) :
    signatureSlots types = Interp.valueTypeSlots types := by
  have same : Itasca.Translate.valueType = Interp.sourceType := by
    funext ty
    cases ty <;> rfl
  simp [signatureSlots, Interp.valueTypeSlots, same]

@[step] theorem compiler_type_slots (types : Slice Itasca.types.ValueType) :
    runtime.compiler.type_slots types ⦃ result =>
      match result with
      | .Ok word => word.val = signatureSlots types.val
      | .Err error => error = .Host ∧ U32.max < signatureSlots types.val ⦄ := by
  unfold runtime.compiler.type_slots
  step with Interp.value_type_slots types as ⟨slots, hs⟩
  rw [← signatureSlots_eq] at hs
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

def SignatureTable (signatures : Slice runtime.compiler.Signature) (types : List functype) : Prop :=
  ∀ (i : Nat) (signature : runtime.compiler.Signature), signatures.val[i]? = some signature →
    ∃ params results : List valtype, types[i]? = some (.mk_functype (.mk_list params) (.mk_list results)) ∧
      SignatureMatches signature params results

/-- Capturing an accepted module type appends its exact value and word counts.
The slot accumulator is total, and rejects only a width above the u32 bound. -/
@[step] theorem capture_signature {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (index : Usize) (ty : Itasca.types.FuncType)
    (lookup : env.types.val[index.val]? = some ty)
    (fits : scheduler.signatures.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ out =>
      out.1 = .Ok () → ∃ signature budget,
        out.2 = { scheduler with signatures := out.2.signatures, budget } ∧
        out.2.signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (ty.params.val.map Itasca.Translate.valueType)
          (ty.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.module.Env.impl.types, bind_ok]
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
      · simp only [runtime.compiler.visitor_result, bind_ok, WP.spec_ok]
        intro accepted
        refine ⟨_, scheduler.budget, rfl, appended, ?_⟩
        constructor
        · simp [alloc.vec.Vec.len]
        · simp [alloc.vec.Vec.len]
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hparams
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hresults
      · simp [runtime.compiler.visitor_result]
end Itasca.Runtime.Code
