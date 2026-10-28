import Exec.Code.Local.Relations.Common.Signatures
/-! The actual scheduler loop constructs a source-aligned signature table
from every module type, retaining exact value and word arities. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def SignatureSequence (signatures : List runtime.compiler.Signature)
    (types : List Itasca.types.FuncType) : Prop :=
  List.Forall₂ (fun signature ty => SignatureMatches signature
    (ty.params.val.map Itasca.Translate.valueType) (ty.results.val.map Itasca.Translate.valueType)) signatures types

theorem SignatureSequence.append {signatures types signature ty}
    (before : SignatureSequence signatures types)
    (last : SignatureMatches signature (ty.params.val.map Itasca.Translate.valueType)
      (ty.results.val.map Itasca.Translate.valueType)) :
    SignatureSequence (signatures ++ [signature]) (types ++ [ty]) := by
  induction before with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

theorem SignatureSequence.lookup {signatures types}
    (sequence : SignatureSequence signatures types) {index : Nat} {signature : runtime.compiler.Signature}
    (found : signatures[index]? = some signature) :
    ∃ ty : Itasca.types.FuncType, types[index]? = some ty ∧ SignatureMatches signature
      (ty.params.val.map Itasca.Translate.valueType) (ty.results.val.map Itasca.Translate.valueType) := by
  induction sequence generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst signature
              exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

theorem SignatureSequence.table {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.types.FuncType} (sequence : SignatureSequence signatures.val types) :
    SignatureTable signatures (types.map Itasca.EnvTranslation.funcType) := by
  intro index signature found
  obtain ⟨ty, lookup, matched⟩ := SignatureSequence.lookup sequence found
  refine ⟨_, _, ?_, matched⟩
  simp [List.getElem?_map, lookup, Itasca.EnvTranslation.funcType]

@[step] theorem capture_signatures_loop_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.types.val.length)
    (prefixMatches : status = .Ok () → SignatureSequence scheduler.signatures.val (env.types.val.take index.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index status ⦃ out =>
      out.2.2.2.2.2.2.2 = .Ok () → SignatureSequence out.1.val env.types.val ∧
        out.2.1 = scheduler.func_param_slots ∧ out.2.2.2.1 = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun p => env.types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.types.val.length ∧
      (p.2.2 = .Ok () → SignatureSequence p.1.signatures.val (env.types.val.take p.2.1.val) ∧
        p.1.func_param_slots = scheduler.func_param_slots ∧ p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.module.Env.impl.types, bind_ok]
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
        step with capture_signature ops law current env i env.types.val[i.val]
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
end Itasca.Runtime.Code
