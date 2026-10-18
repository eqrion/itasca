import Exec.Representation.Values

/-! Argument checking tests scalar tags and the owning-store identity of
references. Address validity is a separate store/issued-handle invariant. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

noncomputable section
local instance : DecidableEq Itasca.types.ValueType := Classical.decEq _

def OwnedBy (id : Usize) : runtime.Value → Prop
  | .FuncRef (some address) => address.store = id
  | .ExternRef (some address) => address.store = id
  | _ => True

def ArgumentMatches (id : Usize) (value : runtime.Value) (ty : Itasca.types.ValueType) : Prop :=
  OwnedBy id value ∧ rawType value = ty

noncomputable def checkOwner (id : Usize) (value : runtime.Value) :
    core.result.Result Unit runtime.ExecError := by
  classical
  exact if OwnedBy id value then .Ok () else .Err .WrongStore

noncomputable def checkArgument (id : Usize) (value : runtime.Value)
    (ty : Itasca.types.ValueType) : core.result.Result Unit runtime.ExecError := by
  classical
  exact if OwnedBy id value then
    if rawType value = ty then .Ok () else .Err .BadArguments
  else .Err .WrongStore

noncomputable def checkArguments (id : Usize) : List runtime.Value → List Itasca.types.ValueType →
    core.result.Result Unit runtime.ExecError
  | [], [] => .Ok ()
  | value :: values, ty :: types =>
      match checkArgument id value ty with
      | .Ok _ => checkArguments id values types
      | .Err error => .Err error
  | _, _ => .Err .BadArguments

theorem checkArgument_ok_iff (id : Usize) (value : runtime.Value) (ty : Itasca.types.ValueType) :
    checkArgument id value ty = .Ok () ↔ ArgumentMatches id value ty := by
  classical
  simp [checkArgument, ArgumentMatches]
  split <;> simp_all

theorem checkArguments_ok_iff (id : Usize) (values : List runtime.Value)
    (types : List Itasca.types.ValueType) :
    checkArguments id values types = .Ok () ↔ List.Forall₂ (ArgumentMatches id) values types := by
  induction values generalizing types with
  | nil => cases types <;> simp [checkArguments]
  | cons value values ih =>
    cases types with
    | nil => simp [checkArguments]
    | cons ty types =>
      simp only [checkArguments, List.forall₂_cons]
      have hok := checkArgument_ok_iff id value ty
      cases hc : checkArgument id value ty with
      | Ok unit =>
        cases unit
        have hm : ArgumentMatches id value ty := hok.mp hc
        simpa [hm] using ih types
      | Err error => simp_all

@[step] theorem check_value_eq {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (value : runtime.Value) :
    runtime.store.Store.check_value memory store value ⦃ out => out = checkOwner store.id value ⦄ := by
  cases value <;> simp only [runtime.store.Store.check_value, checkOwner, OwnedBy]
  all_goals try simp
  all_goals cases ‹Option _› <;> simp [runtime.store.Store.check, checkOwner, OwnedBy]
  all_goals split <;> simp_all

@[step] theorem value_type_eq (value : runtime.Value) :
    runtime.Value.value_type value ⦃ out => out = rawType value ⦄ := by
  cases value <;> simp [runtime.Value.value_type, rawType]

theorem value_type_ne_eq (left right : Itasca.types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType left right =
      .ok (if left = right then false else true) := by
  classical
  cases left <;> cases right <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, types.ValueType.Insts.CoreCmpPartialEqValueType,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
      Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step] theorem value_type_ne_spec (left right : Itasca.types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType left right
      ⦃ out => out = if left = right then false else true ⦄ := by
  rw [value_type_ne_eq]
  simp

def checkSequence (first rest : core.result.Result Unit runtime.ExecError) :
    core.result.Result Unit runtime.ExecError :=
  match first with
  | .Ok _ => rest
  | .Err error => .Err error

@[step] theorem check_values_loop_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.types.ValueType)
    (position : Usize) (status : core.result.Result Unit runtime.ExecError)
    (lengths : values.length = types.length) (bound : position.val ≤ values.length) :
    runtime.interp.check_values_loop memory store values types position status
      ⦃ out => out = checkSequence status
        (checkArguments store.id (values.val.drop position.val) (types.val.drop position.val)) ⦄ := by
  unfold runtime.interp.check_values_loop
  apply loop.spec_decr_nat (fun p => values.length - p.1.val)
    (fun p => p.1.val ≤ values.length ∧
      checkSequence p.2 (checkArguments store.id (values.val.drop p.1.val) (types.val.drop p.1.val)) =
        checkSequence status (checkArguments store.id (values.val.drop position.val) (types.val.drop position.val)))
  · rintro ⟨index, current⟩ ⟨hi, hcheck⟩
    dsimp only at hi hcheck
    unfold runtime.interp.check_values_loop.body
    dsimp only
    split
    · have hv : index.val < values.val.length := by change index.val < values.length; scalar_tac
      have ht : index.val < types.val.length := by change index.val < types.length; scalar_tac
      cases current with
      | Err error => simpa [core.result.Result.is_ok, checkSequence] using hcheck
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        simp only [checkSequence] at hcheck
        rw [List.drop_eq_getElem_cons hv, List.drop_eq_getElem_cons ht] at hcheck
        step as ⟨value, hvalue⟩
        step with check_value_eq memory store value as ⟨result, hresult⟩
        subst result
        by_cases owned : OwnedBy store.id value
        · simp only [checkOwner, owned, ↓reduceIte, core.result.Result.is_ok, bind_ok]
          step with value_type_eq value as ⟨actualType, htype⟩
          subst actualType
          step as ⟨expectedType, hexpected⟩
          rw [value_type_ne_eq]
          split
          · rename_i matching
            simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
            step as ⟨next, hnext⟩
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            simpa [checkSequence, checkArguments, checkArgument, ← hvalue, ← hexpected,
              owned, matching, hnext] using hcheck
          · rename_i mismatch
            simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
            step as ⟨next, hnext⟩
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            simpa [checkSequence, checkArguments, checkArgument, ← hvalue, ← hexpected,
              owned, mismatch] using hcheck
        · simp only [checkOwner, owned, ↓reduceIte, core.result.Result.is_ok, bind_ok, Bool.false_eq_true]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simpa [checkSequence, checkArguments, checkArgument, ← hvalue, owned] using hcheck
    · have hend : index.val = values.length := by scalar_tac
      have htypes : index.val = types.length := by omega
      cases current with
      | Err error => simpa [checkSequence] using hcheck
      | Ok unit =>
        cases unit
        have hvdrop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by change values.length ≤ index.val; omega)
        have htdrop : types.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by change types.length ≤ index.val; omega)
        simpa [checkSequence, hvdrop, htdrop, checkArguments] using hcheck
  · exact ⟨bound, rfl⟩

/-- The public checker rejects a length mismatch before inspecting any value;
otherwise it returns the first owner/tag error in argument order. -/
@[step] theorem check_values_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.types.ValueType) :
    runtime.interp.check_values memory store values types ⦃ out =>
      out = if values.length = types.length then checkArguments store.id values.val types.val
        else .Err .BadArguments ⦄ := by
  unfold runtime.interp.check_values
  by_cases he : values.length = types.length
  · have hlen : values.len = types.len := by scalar_tac
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step with check_values_loop_effect memory store values types 0#usize (.Ok ()) he (by simp)
      as ⟨out, hout⟩
    simpa [he, checkSequence] using hout
  · have hlen : (values.len != types.len) = true := by scalar_tac
    simp [hlen, he]

/-- Accepted arguments have precisely the expected tags, and every non-null
reference carries the store's identity. This does not assume valid addresses. -/
theorem check_values_accepts_iff {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.types.ValueType) :
    runtime.interp.check_values memory store values types ⦃ out =>
      out = .Ok () ↔ List.Forall₂ (ArgumentMatches store.id) values.val types.val ⦄ := by
  step with check_values_effect memory store values types as ⟨out, hout⟩
  subst out
  split
  · exact checkArguments_ok_iff store.id values.val types.val
  · rename_i hn
    constructor
    · intro h; cases h
    · intro h
      exact False.elim (hn h.length_eq)

end
end Exec.Interp
