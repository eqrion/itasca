import Exec.Code.Local.Callbacks.Control.EnterBlock
import Exec.Code.Local.Control.Common.Structured
import Itasca.Support.ControlTranslation
/-! Compiler signature capture: total exact word counting, retained source
value/word arities, and source block-signature resolution. -/
namespace Exec.Code
open Aeneas Aeneas.Std

def signatureSlots (types : List Itasca.types.ValueType) : Nat :=
  slots (types.map Itasca.Translate.valueType)

def SignatureCount (types : List Itasca.types.ValueType) (total : Nat)
    (amount : U32) (index : Usize) (overflow : Bool) : Prop :=
  if overflow then U32.max < total else amount.val + signatureSlots (types.drop index.val) = total

@[step] theorem compiler_type_slots_loop (types : Slice Itasca.types.ValueType)
    (amount : U32) (index : Usize) (overflow : Bool) (total : Nat)
    (bound : index.val ≤ types.val.length)
    (state : SignatureCount types.val total amount index overflow) :
    runtime.compiler.type_slots_loop types amount index overflow ⦃ out =>
      if out.2 then U32.max < total else out.1.val = total ⦄ := by
  unfold runtime.compiler.type_slots_loop
  apply loop.spec_decr_nat (fun p => types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ types.val.length ∧ SignatureCount types.val total p.1 p.2.1 p.2.2)
  · rintro ⟨amount, i, overflow⟩ ⟨hi, hs⟩
    dsimp only at hi hs
    unfold runtime.compiler.type_slots_loop.body
    dsimp only
    split
    · rename_i more
      have hb : i.val < types.val.length := by scalar_tac
      cases overflow with
      | true => simpa [SignatureCount] using hs
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        simp only [SignatureCount, Bool.false_eq_true, ite_false] at hs
        rw [List.drop_eq_getElem_cons hb] at hs
        simp only [signatureSlots, List.map_cons, slots] at hs
        step as ⟨ty, hty⟩
        step with compiler_width ty as ⟨word, hword⟩
        step as ⟨sum, hsum⟩
        cases sum with
        | none =>
          simp only [bind_ok, uncurry_apply_pair]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [SignatureCount, ite_true]
          rw [← hty] at hs
          scalar_tac
        | some sum =>
          simp only [bind_ok, uncurry_apply_pair]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [SignatureCount, Bool.false_eq_true, ite_false, hnext, signatureSlots]
          rw [← hty] at hs
          scalar_tac
    · rename_i finished
      have same : i.val = types.val.length := by scalar_tac
      cases overflow <;> simpa [SignatureCount, same, signatureSlots, slots] using hs
  · exact ⟨bound, state⟩

@[step] theorem compiler_type_slots (types : Slice Itasca.types.ValueType) :
    runtime.compiler.type_slots types ⦃ result =>
      match result with
      | .Ok word => word.val = signatureSlots types.val
      | .Err error => error = .Host ∧ U32.max < signatureSlots types.val ⦄ := by
  unfold runtime.compiler.type_slots
  step with compiler_type_slots_loop types 0#u32 0#usize false (signatureSlots types.val)
    (by simp) (by simp [SignatureCount]) as ⟨amount, overflow, hs⟩
  cases overflow <;> simpa using hs

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

/-- The selected concrete signature gives exactly the source block signature
and all four value/word arities, including indexed multi-value blocks. -/
theorem SignatureAt.source {signatures bt signature types}
    (selected : SignatureAt signatures bt signature) (table : SignatureTable signatures types) :
    ∃ params results, BlockSignature types (Itasca.Wasm2.blockType bt) params results ∧
      SignatureMatches signature params results := by
  cases selected with
  | empty => exact ⟨[], [], .empty, by constructor <;> rfl⟩
  | value ty word width =>
    refine ⟨[], [Itasca.Translate.valueType ty], .value _, ?_⟩
    constructor <;> simp_all [slots]
  | index i signature found =>
    obtain ⟨params, results, lookup, matched⟩ := table i.val signature found
    exact ⟨params, results, .index i.val params results lookup, matched⟩
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
  simp only [module.Env.types, Itasca.module.Env.impl.types, bind_ok]
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
end Exec.Code
